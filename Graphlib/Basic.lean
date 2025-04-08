/-
Copyright (c) 2025 Simone Kilian. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simone Kilian, Supervisor: Malvin Gattinger
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.FinEnum
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Weighted Digraphs

This module defines directed graphs on a vertex type `V` and edge type `E`,
which is the same notion as a relation `payload : (u : V) -> (v : V) -> (Adj u v) -> E`.
This approach extends the Digraph structure, using `Adj u v` from Digraph as a proof
for the adjacency relation.

Note that a weighted digraph may have self loops.

Every edge present in the graph, i.e. where `Adj u v` is returning the decidable Prop `true`,
is associated with an edge label (weight).
This label can be used for various puroses that include, for example, multiedge weights via
`List W` for some type `W`, finite set type, or `Nat`, but also for labeling with propositions
and formulae.
-/


/-- A weighted digraph is a relation `Payload` on a vertex type `V`, a `Prop` and the last
coordinate of label type `E`. Note that a tuple only exists if the decidable `Adj u v` returns
true.
The relation `Adj u v` describes which pairs of vertices are adjacent and is inherited from Digraph.
Since this definition of digraphs is aimed to study algorithms, we force this relation to be #
decidable with `instDecAdj : DecidableRel Adj`.
-/
structure WeightedDiGraph (V : Type) (E : Type) [FinEnum V] extends Digraph V where
  Payload : (u : V) -> (v : V) -> (Adj u v) -> E
  instDecAdj : DecidableRel Adj


-- def local global variable for a graph
variable {V : Type} {E : Type} [FinEnum V] [DecidableEq V] [DecidableEq E]
variable (G : WeightedDiGraph V E)

/--  A `walk` is a sequence of adjacent vertices.  For vertices `u v : V`,
the type `walk u v` consists of all walks starting at `u` and ending at `v`. -/
inductive Walk : V → V → Type
  | nil {u : V} : Walk u u
  | cons {f w t : V} (h : (G.Adj f w)) (p : Walk w t) : Walk f t
  deriving DecidableEq
-- h is hypothese for valid edge, f from node, w next node of starting walk, t to node, p rest node from w to t

attribute [refl] Walk.nil

/-- `Support` of a walk is the list of edges it visits in order. -/
def support {u v : V} : (Walk G u v) → List V
  | @Walk.cons _ _ _ _ u _ _ _ rest => u :: support rest
  | Walk.nil => [v]

/-- A `path` is a walk with no repeating vertices. -/
structure Path (u : V) (v : V) where
  walk : Walk G u v
  support_nodup : List.Nodup (support G walk)
  deriving DecidableEq

/-- `append` takes two walks `w1 : Walk G u v` and `w2 : Walk G v w` and returns the
appended walk `Walk G u w` -/
def append (w1 : Walk G u v) (w2 : Walk G v w) : Walk G u w :=
  match w1 with
  | Walk.nil => w2
  | Walk.cons h p => Walk.cons h (append p w2)

/-- `extend_walk` takes a walk `ww : Walk G u v` and a proof `h : G.Adj v w` for adjacency of
vertices `v` and the vertex that should be added at the end of the walk `w` and returns an
extended walk `Walk G u w`-/
def extend_walk (ww : Walk G u v) (h : G.Adj v w) : Walk G u w :=
  append G ww (Walk.cons h Walk.nil)


-- theorems for `List.Pairwise`. Needed for extension of Paths with new edges, due to need to modify Nodup proofs.
theorem pairwise_add_anywhere {α: Type} {pr: α → α → Prop} {l1 l2 : List α} {symm: Symmetric pr} {a : α}:
    (∀ (a' : α), a' ∈ l1 ∨ a' ∈ l2 → pr a a') ∧ (List.Pairwise pr (l1 ++ l2))
    → (List.Pairwise pr (l1 ++ (a :: l2)))   := by
    intro ⟨ allhold, rest_of_list ⟩
    induction l1
    case nil =>
      simp
      simp at rest_of_list
      constructor
      case left =>
        intro a'
        intro inl2
        apply allhold
        right
        exact inl2
      case right => exact rest_of_list
    case cons l ls IH =>
      simp
      constructor
      case left =>
        intro a'
        intro cond
        by_cases isa : a' = a
        case pos =>
          apply symm
          simp [isa]
          apply allhold
          left
          simp
        case neg =>
          simp at rest_of_list
          have ⟨ all_condition, rest_list⟩ := rest_of_list
          apply all_condition
          cases cond
          case a.inl apinls =>
            left
            exact apinls
          case a.inr some_or =>
          cases some_or
          case inl apisa =>
            contradiction
          case inr apinl2 =>
            right
            exact apinl2
      case right =>
        apply IH
        · intro a'
          intro stuff
          apply allhold
          cases stuff
          case inl ainls =>
            left
            simp
            right
            exact ainls
          case inr ainl2=>
            right
            exact ainl2
        · simp at rest_of_list
          have ⟨ all, rest⟩ := rest_of_list
          exact rest


theorem pairwise_additional_does_not_matter {α: Type} {pr: α → α → Prop} {l1 l2 : List α} {a : α}:
    (List.Pairwise pr (l1 ++ (a :: l2))) → (List.Pairwise pr (l1 ++ l2)) := by
    induction l1
    case nil =>
      simp
    case cons l l1s IH =>
      intro longList
      simp
      constructor
      case left =>
        intro b
        intro condition
        simp at longList
        cases condition
        case inl binl1s =>
          have foo := longList.left
          apply foo
          left
          exact binl1s
        case inr binl2 =>
          have foo := longList.left
          apply foo
          right
          right
          exact binl2
      case right =>
        apply IH
        simp at longList
        exact longList.right

theorem pairwise_elem_after {α: Type} {pr: α → α → Prop} {l1 l2 : List α} {x a : α}:
    (List.Pairwise pr (l1 ++ (a :: l2))) ∧ (x ∈ l2) → pr a x := by
    intro ⟨ full_list_pairwise, xinl2 ⟩
    induction l1
    case nil => simp_all
    case cons l lss IH =>
      simp at full_list_pairwise
      apply IH
      exact full_list_pairwise.right

theorem pairwise_elem_before {α: Type} {pr: α → α → Prop} {l1 l2 : List α} {x a : α}:
    (List.Pairwise pr (l1 ++ (a :: l2))) ∧ (x ∈ l1) → pr x a := by
    intro ⟨ full_list_pairwise, xinl1 ⟩
    induction l1
    case nil => simp_all
    case cons l lss IH =>
      simp at full_list_pairwise
      have ⟨ all, rest_of_list ⟩ := full_list_pairwise
      simp at xinl1
      cases xinl1
      case inl xisl =>
        rw [xisl]
        apply all
        right
        left
        rfl
      case inr xinRest =>
        apply IH
        · exact rest_of_list
        · exact xinRest


theorem switched_lists_under_pairwise_eq {α: Type} {pr: α → α → Prop} {symm: Symmetric pr} {l1 l2 : List α}:
    (List.Pairwise pr (List.append l1 l2)) = (List.Pairwise pr (List.append l2 l1)) := by -- pr = predicate that all pairs in pairwise have to satisfy
    simp [append]
    induction l1
    case nil =>
      simp
      --apply List.nil_append
      --apply List.append_nil
      --rfl
    case cons l ls IH =>
      simp [List.Pairwise]
      constructor
      · intro cond
        let ⟨ q, sublist⟩ := cond
        clear cond
        let ⟨ ihl, ihr ⟩ := IH
        clear IH
        let qq := ihl sublist
        apply pairwise_add_anywhere
        exact symm  -- apply the proof that pr is symmetric
        constructor
        · intro a' a
          simp_all only [imp_self]
          cases a with
          | inl h => simp_all only [or_true]
          | inr h_1 => simp_all only [true_or]
        · exact qq
      · intro cond
        constructor
        · intro x
          intro or
          cases or
          case inl ha =>
            apply @pairwise_elem_after α pr l2 ls
            constructor
            · exact cond
            · exact ha
          case inr ha =>
            apply symm
            apply @pairwise_elem_before α pr l2 ls
            constructor
            · exact cond
            · exact ha
        · simp [IH]
          exact pairwise_additional_does_not_matter cond


/-- theorem `extend_walk_support_node_added_at_end`: support of extended walk is the
same as the support list of the old walk ectended by one -/
theorem extend_walk_support_node_added_at_end
     [FinEnum V'] {G : WeightedDiGraph V' E'} {h : G.Adj v w} { www : Walk G a v } :
    (support G (extend_walk G www h)) = List.append (support G www) [w]  := by
    rw [extend_walk]
    induction www
    case nil =>
      simp [append]
      simp [support]
    case cons hh pp IH =>
      simp [append]
      simp [support]
      apply IH



/-- `extend_path` takes a uv path `p :Path G u v`, a proof `h : G.Adj v w` that an vw edge exists
  and a proof `proof_w_not_in_support : w ∉ support G p.walk` that w is not part of the path yet and
  returns a path extended by w -/
def extend_path (p : Path G u v) (h : G.Adj v w) (proof_w_not_in_support : w ∉ support G p.walk) : Path G u w :=
  let path_walk := extend_walk G p.walk h
  let set_eq : (support G path_walk) = List.append (support G p.walk) [w]  := by
    simp [path_walk]
    rw [extend_walk]
    clear path_walk
    clear proof_w_not_in_support
    apply extend_walk_support_node_added_at_end

  let path_nodup : List.Nodup (support G path_walk) := by
    simp [List.Nodup]
    rw [set_eq]
    rw [switched_lists_under_pairwise_eq]
    simp [List.append]
    apply And.intro
    ·
      intro a ha
      intro wa
      subst wa
      simp_all only [not_true_eq_false]
    exact p.support_nodup
    -- we need to prove that the ≠ function that occurs in nodup is symmetric (otherwise one of our helper theorems does not hold any more)
    simp [Symmetric]
    intro x y
    intro notEq
    intro h
    apply notEq
    rw  [h]
  Path.mk path_walk path_nodup -- constructor new path

omit [DecidableEq V] [DecidableEq E] in
theorem extend_walk_extends_support (ww: Walk G u v) (h: G.Adj v w):
  support G (extend_walk G ww h) = (support G ww) ++ [w] :=
  by
    induction ww
    case nil =>
      unfold extend_walk
      unfold append
      unfold support
      unfold support
      simp
    case cons hh restP IH =>
      unfold extend_walk
      unfold append
      unfold support
      unfold extend_walk at IH
      simp
      apply IH

omit [DecidableEq V] [DecidableEq E] in
theorem extend_path_extends_support (p: Path G u v) (h: G.Adj v w)(proof_w_not_in_support : w ∉ support G p.walk):
   support G (extend_path G p h proof_w_not_in_support).walk = (support G p.walk) ++ [w]  := by
      unfold extend_path
      simp
      apply extend_walk_extends_support





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
    if h : s.node = goal then some (by
      subst h
      exact s.path
      )
    else
      let u : Finset V := Finset.univ
      let l0 : List V := FinEnum.toList u
      let newly_visited : Finset V := Finset.filterMap
       (λ v =>
          let edgePresent := g.instDecAdj s.node v
          let edge : Prop := g.Adj s.node v -- proof edge is there
          if d : decide edge ∧ v ∉ visited then -- here check condition if not in visited
             some v
          else
            none -- edge does not exist
      ) Finset.univ (by
        intro a a' b a_1 a_2
        simp_all only [decide_eq_true_eq, dite_eq_ite, Option.mem_def, Option.ite_none_right_eq_some, Option.some.injEq]
      ) -- filter neighbors to expand the visited list

      let new_visited := visited ∪ newly_visited

      let new_nodes_neighbors : List (NodePathPair g start new_visited):= List.filterMap
       (λ v =>
         if notVisited : v ∉ visited then
           -- get the proof that determining the edge between s.node and v is decidable. We need this later when we decide edge
          let edgePresent := g.instDecAdj s.node v
          let edge : Prop := g.Adj s.node v -- proof edge is there
          if d : decide edge then
            let oldpath : Path g start s.node := s.path
            let w : Path g start v := extend_path g oldpath (by
              exact of_decide_eq_true d
            ) (by
              let oldpath_proof : (support g s.path.walk).toFinset ⊆ visited := s.reached_nodes_proofs
              simp [oldpath]
              rw [← List.mem_toFinset]
              apply Set.not_mem_subset
              exact oldpath_proof
              exact notVisited
            )
            let r : NodePathPair g start new_visited := NodePathPair.mk v w (by -- proof that support(path) ⊆ new_visisted
              simp [new_visited]

              simp [w]
              simp [extend_path_extends_support]
              apply Finset.union_subset_union
              exact s.reached_nodes_proofs
              simp_all only [decide_eq_true_eq, dite_eq_ite, Finset.singleton_subset_iff, Finset.mem_filterMap, Finset.mem_univ, Option.ite_none_right_eq_some, Option.some.injEq, true_and, exists_eq_right, oldpath, w, new_visited, edge, newly_visited]
              simp
              exact of_decide_eq_true d
            )
            r
          else
            none -- edge does not exist
        else
          none -- target node has already been visited
      ) l0 -- filter neighbors to expand stack

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
          apply Finset.eq_empty_of_forall_not_mem
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
        rw [Finset.eq_empty_iff_forall_not_mem] at no_new_visited
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
        simp_all only [Finset.not_mem_empty]
        simp_all [Finset.subset_univ]

        -- second half of the Lex.left
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset]
        rw [Finset.eq_empty_iff_forall_not_mem] at no_new_visited
        simp at no_new_visited
        apply Exists.elim no_new_visited
        intro b
        intro bInNewlyVisited
        exists b
        apply And.intro
        simp
        right
        simp [newly_visited] at bInNewlyVisited
        exact bInNewlyVisited
        intro bInVisited
        have bInIntersect : b ∈ visited ∩ newly_visited := by
          apply Finset.mem_inter_of_mem
          exact bInVisited
          exact bInNewlyVisited
        simp_all only [Finset.not_mem_empty]
        simp_all [Finset.subset_univ]



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

theorem dfs_is_complete(g: WeightedDiGraph V E) (start : V) (goal : V) :
    ((∃ x : (Path g start goal), x = x) → Option.isSome (dfs g start goal)) := by -- or Option.isNone (dfs g start goal) → ∄ x (Path g start goal), x = x
      intro walk_exists
      apply Exists.elim walk_exists
      intro theWalk
      intro
      unfold dfs
      sorry



-- current further ideas:
-- possible invariants:
--$\forall v \in $ \texttt{visited} $\setminus $  \texttt{vertices(stack) :}  \texttt{neighbors(v)} $ \subseteq $ \texttt{visited}
-- h: $\forall $ \texttt{paths(start,goal)} $\exists v \in $ \texttt{vertices(stack) :}  \texttt{isPath(v,goal)}
-- return (pfad, h (h= hyp), maybe the stack, but then also visited set
-- or with mutual block mutual inner_dfs .. theorem end, and later call theorem in completeness proof
-- rewrite algorithm?:
-- using state monads to simulate step function, make outside a step function for a call on each step, try to use kind of a loop





-- tests

def graph1 : WeightedDiGraph (Fin 3) (Nat) where
  Adj := fun f t =>
    match (f,t) with
     | (0,1) => true
     | (1,2) => true
     | (2,1) => true
     | (_,_) => false
  Payload := fun f t h => by
      by_cases hf0: f = 0
      <;> by_cases hf1: f = 1
      <;> by_cases hf2: f = 2
      <;> by_cases ht0: t = 0
      <;> by_cases ht1: t = 1
      <;> by_cases ht2: t = 2
      -- now we have 64 goals
      <;> try omega
      all_goals simp_all
      exact 3 -- 0 1 edge
      exact 4 -- 1 2 edge
      exact 5 -- 2 1 edge

  instDecAdj := fun a b => by
    simp
    obtain ⟨ va, lta ⟩ := a
    obtain ⟨ vb, ltb ⟩ := b
    cases va
    case zero =>
      cases vb
      case zero => simp; exact instDecidableFalse
      case succ n =>
        cases n
        case zero => simp; exact instDecidableTrue
        case succ n' => simp; exact instDecidableFalse
    case succ n =>
      cases vb
      case zero => simp; exact instDecidableFalse
      case succ nb =>
        cases n
        case zero =>
          simp
          cases nb
          case zero => simp; exact instDecidableFalse
          case succ nb'' =>
            cases nb''
            case zero => simp; exact instDecidableTrue
            case succ nb3 => simp; exact instDecidableFalse
        case succ n' =>
          cases n'
          case succ n'' => simp; exact instDecidableFalse
          case zero =>
            simp
            cases nb
            case zero => simp; exact instDecidableTrue
            case succ x => simp; exact instDecidableFalse

#eval List.dropLast [1, 2, 3, 4]  -- Output: [1, 2, 3]

--#eval graph1.Adj 1 0 -- none
--#eval dfs graph1 1 0  -- false
--#eval dfs graph1 0 2  -- true
--#eval Finset.toList (neighbors graph1 1)
--#eval neighbors graph1 1
--#eval is_valid_path graph1 [1,2]   --true
--#eval is_valid_path graph1 [0,1,2] --true
--#eval is_valid_path graph1 [1,2,3] --false
--#eval is_valid_path graph1 [1,2,1] --false
