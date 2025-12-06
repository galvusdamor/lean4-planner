import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Data.Bool.AllAny
import Mathlib.Data.FinEnum

import Graphlib.Lists

set_option trace.split.failure true


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

/-- `Length` of a walk is the number of edges in it-/
def walk_length {u v : V} : (Walk G u v) → ℕ
  | @Walk.cons _ _ _ _ _ _ _ _ rest => 1 + walk_length rest
  | Walk.nil => 0


/-- A `path` is a walk with no repeating vertices. -/
structure Path (u : V) (v : V) where
  walk : Walk G u v
  support_nodup : List.Nodup (support G walk)
  deriving DecidableEq


def nil_path (u : V) : Path G u u :=
  let w : Walk G u u := Walk.nil
  have p : List.Nodup (support G w) := by
    unfold w
    unfold support
    simp

  Path.mk w p


def path_length {u v : V} (p : Path G u v) : ℕ := walk_length G p.walk

--lemma paths_length_le_V_card_min_1 {u v : V} (p : Path G u v) : path_length G p ≤ Fintype.card V - 1 := by 
--  sorry


/-- Definition of `Shortest Path` -/
def path_is_shortest {u v : V} (p : Path G u v) : Prop :=
  ∀ p' : Path G u v, path_length G p ≤ path_length G p'



def is_sub_walk_head {u v w : V} (p : Walk G u v) (p' : Walk G w v) : Bool :=
  if u = w then true
  else match p with
  | Walk.nil => false
  | Walk.cons _ p_sub => is_sub_walk_head p_sub p'

def is_sub_walk_tail {u v w : V} (p : Walk G u v) (p' : Walk G u w) : Bool :=
  match p' with 
  | Walk.nil => true -- p' is the empty path already.
  | Walk.cons (w:= p'_u') _ p_sub' =>
    match p with
    | Walk.nil => false -- p' is longer than p
    | Walk.cons (w := p_u') _ p_sub =>
      if h : p_u' = p'_u' then is_sub_walk_tail p_sub (h ▸ p_sub')
      else false

def is_sub_path_tail {u v w : V} (p : Path G u v) (p' : Path G u w) : Bool :=
  is_sub_walk_tail G p.walk p'.walk


--lemma subpath_of_shortest_path_are_shortest {u v w : V} (p : Path G u v) (p_shortest : path_is_shortest G p) (p' : Path G u w) (sub_path : is_sub_path_tail G p p') : path_is_shortest G p' := by
--  by_contra not_shortest
--  unfold path_is_shortest at p_shortest not_shortest
--  simp_all
--  obtain ⟨ shorter_path', is_shorter'⟩ := not_shortest
--  sorry



def graph_distance_is (u v : V) (dist: ℕ) : Prop :=
  (∃ p : Path G u v, path_length G p = dist ∧ path_is_shortest G p)

def graph_distance_ge (u v : V) (dist: ℕ) : Prop :=
  ∀ p : Path G u v, path_length G p ≥ dist

def graph_distance_gt (u v : V) (dist: ℕ) : Prop :=
  ∀ p : Path G u v, path_length G p > dist

def graph_distance_lt (u v : V) (dist: ℕ) : Prop :=
  ∃ p : Path G u v, path_length G p < dist

--lemma shortest_path_shorter_than_example_path (u v : V) (p : Path G u v):
--    ∃ d : ℕ, d ≤ path_length G p ∧ graph_distance_is G u v d := by
--  by_contra distance_is_longer
--  simp_all
--  sorry

omit [DecidableEq V] [DecidableEq E] in
lemma graph_distance_ge_lt (u v : V) (d1 d2: ℕ) :
    graph_distance_ge G u v d1 ∧ d2 ≤ d1 → graph_distance_ge G u v d2
    := by
    unfold graph_distance_ge
    simp_all
    intro ge_d1 d2_le_d1 p
    apply le_trans
    · exact d2_le_d1
    · exact ge_d1 p



-----------------------------------------
-- Operations that modify paths and walks
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


--theorem append_eq_append (w1 : Walk G u v) (w2 : Walk G v w) (w1' : Walk G u v') (w2' : Walk G v' w) (v_eq_v' : v = v'):
--    w1 = v_eq_v' ▸ w1' ∧ w2 = v_eq_v' ▸ w2' →
--    append G w1 w2 = append G w1' w2' := by sorry

/-- Support of extended walk is the same as the support list of the old walk ectended by one. -/
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
    simp only [List.append_eq]
    rw [List.pairwise_append_comm]
    simp only [List.cons_append]
    simp only [List.nil_append]
    simp only [List.pairwise_cons]
    apply And.intro
    ·
      intro a ha wa
      subst wa
      simp_all only [not_true_eq_false]
    exact p.support_nodup
    -- we need to prove that the ≠ function that occurs in nodup is symmetric (otherwise one of our helper theorems does not hold any more)
    intro x y notEq h
    apply notEq
    rw  [h]
  Path.mk path_walk path_nodup -- constructor new path


omit [DecidableEq V] [DecidableEq E] in
theorem append_inc_length_by_one (ww : Walk G u v) (h : G.Adj v w) :
  walk_length G (append G ww (Walk.cons h Walk.nil)) = 1 + walk_length G ww := by
  unfold append
  split
  · unfold walk_length
    unfold walk_length
    simp
  · unfold walk_length
    apply IsLeftCancelAdd.add_left_cancel
    · simp
      apply append_inc_length_by_one
    · use 0


omit [DecidableEq V] [DecidableEq E] in
theorem extend_walk_inc_length_by_one (p : Walk G u v) (h : G.Adj v w) : walk_length G (extend_walk G p h) = 1 + walk_length G p := by
  unfold extend_walk
  apply append_inc_length_by_one

omit [DecidableEq V] [DecidableEq E] in
theorem extend_path_inc_length_by_one (p : Path G u v) (h : G.Adj v w) (proof_w_not_in_support : w ∉ support G p.walk) : path_length G (extend_path G p h proof_w_not_in_support) = 1 + path_length G p := by
  apply extend_walk_inc_length_by_one



theorem split_path_at_end (p : Path G u v) (not_nil : u ≠ v):
    ∃ w : V, ∃ p' : Path G u w, ∃ w_adj_v : G.Adj w v, ∃ not_in_supp : v ∉ support G p'.walk,
      p = extend_path G p' w_adj_v not_in_supp := by
    sorry

theorem paths_contain_sub_paths {u v w : V} (p : Path G u v) (w_in_path : w ∈ support G p.walk) (w_ne_v : w ≠ v):
    ∃ p' : Path G u w, path_length G p' < path_length G p := by sorry




omit [DecidableEq V] [DecidableEq E] in
theorem extend_walk_extends_support (ww: Walk G u v) (h: G.Adj v w):
    support G (extend_walk G ww h) = (support G ww) ++ [w] := by
  induction ww <;> simp_all [extend_walk, append, support]

omit [DecidableEq V] [DecidableEq E] in
theorem extend_path_extends_support (p: Path G u v) (h: G.Adj v w)(proof_w_not_in_support : w ∉ support G p.walk):
   support G (extend_path G p h proof_w_not_in_support).walk = (support G p.walk) ++ [w]  := by
      unfold extend_path
      simp
      apply extend_walk_extends_support

omit [DecidableEq V] [DecidableEq E] in
theorem walk_goal_in_support (p: Walk G u v): v ∈ support G p := by
  unfold support
  split
  · simp
    right
    apply walk_goal_in_support
  · simp

omit [DecidableEq V] [DecidableEq E] in
theorem path_goal_in_support (p: Path G u v): v ∈ support G p.walk := by
  apply walk_goal_in_support

-- tests
example : WeightedDiGraph (Fin 3) (Nat) where
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
