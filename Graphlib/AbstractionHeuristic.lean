import Validator.PlanningTask.Core
import Validator.PlanningTask.Basic
import Graphlib.NatGraph
import Graphlib.Planning
import Graphlib.Heuristics

import Graphlib.temp

import Mathlib.Logic.Lemmas
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Vector.Basic

namespace Validator


------------------------------- Abstraction Heuristics


def is_valid_abstraction {V V': Type} [FinEnum V] [FinEnum V'] (g : NatGraph V) (g' : NatGraph V') (abstraction : V → V') :=
  ∀ v : V, ∀ v' : V, g.Adj v v' → g'.Adj (abstraction v) (abstraction v')


def is_bisimulation {V V': Type} [FinEnum V] [FinEnum V'] (g : NatGraph V) (g' : NatGraph V') (abstraction : V → V') :=
  ∀ v : V, ∀ v' : V, g.Adj v v' ↔ g'.Adj (abstraction v) (abstraction v')




def abstraction_heuristic {n : ℕ} (prob : STRIPS n) {V : Type} [FinEnum V] (g : NatGraph V) (abstraction: State' n → V) (s : State' n) : ℕ :=
  let goals := (trans_of_STRIPS_goals prob).map abstraction
  let opt_ret := NatGraph.astar_multigoal (g:=g) (fun _ => 0) (abstraction s) goals
  match opt_ret with
  | .none => (2^n) * (max_action_cost prob)
  | .some ret =>
      ret.2.val.cost


/- The original statement only requires `is_valid_abstraction`, which preserves edges but
   says nothing about costs.  Admissibility additionally requires that abstract edge costs
   never exceed concrete edge costs; otherwise the abstract shortest path can overestimate.
   We comment out the original and provide a corrected version with the extra cost hypothesis. -/
-- lemma abstractions_admissible {n : ℕ} (prob : STRIPS n) {V : Type} [FinEnum V] {g : NatGraph V} (abstraction: State' n → V) (is_abstraction : is_valid_abstraction (trans_of_STRIPS prob) (g) abstraction) :
--   heur_admissible' prob (fun s => abstraction_heuristic prob g abstraction s)
--     := ...

/-- Map a walk in the concrete graph to a walk in the abstract graph via an abstraction. -/
def map_walk_to_abstract {V1 V2 : Type} [FinEnum V1] [FinEnum V2]
    {G1 : NatGraph V1} {G2 : NatGraph V2}
    (f : V1 → V2) (f_adj : ∀ (a b : V1), G1.Adj a b → G2.Adj (f a) (f b))
    {u v : V1} : G1.Walk u v → G2.Walk (f u) (f v)
  | .nil => .nil
  | .cons adj rest => .cons (f_adj _ _ adj) (map_walk_to_abstract f f_adj rest)

/-
PROBLEM
The cost of the abstract walk is at most the cost of the concrete walk,
    given that abstract edge costs are at most concrete edge costs.

PROVIDED SOLUTION
By induction on w. Base case (nil): both costs are 0. Cons case (cons adj rest): abstract walk cost = edgeCost (f_adj _ _ adj) + (map_walk_to_abstract f f_adj rest).cost. By IH, (map_walk_to_abstract f f_adj rest).cost ≤ rest.cost. By cost_le_hyp, edgeCost (f_adj _ _ adj) ≤ edgeCost adj. So abstract walk cost ≤ edgeCost adj + rest.cost = w.cost. Use add_le_add.
-/
lemma map_walk_cost_le {V1 V2 : Type} [FinEnum V1] [FinEnum V2]
    {G1 : NatGraph V1} {G2 : NatGraph V2}
    (f : V1 → V2) (f_adj : ∀ (a b : V1), G1.Adj a b → G2.Adj (f a) (f b))
    (cost_le_hyp : ∀ (a b : V1) (adj : G1.Adj a b),
      NatGraph.edgeCost (f_adj a b adj) ≤ NatGraph.edgeCost adj)
    {u v : V1} (w : G1.Walk u v) :
    (map_walk_to_abstract f f_adj w).cost ≤ w.cost := by
      induction w <;> simp_all +decide [ NatGraph.edgeCost ];
      · rfl;
      · exact Nat.add_le_add ( cost_le_hyp _ _ ‹_› ) ‹_›

/-- A valid abstraction that also under-approximates edge costs produces an admissible
heuristic.  The additional hypothesis `cost_le` strengthens `is_valid_abstraction` to
require that abstract edge costs are at most the concrete edge costs.
Modified from the original: added `cost_le` hypothesis, without which the statement is
false (a valid abstraction can have arbitrarily high edge costs). -/
lemma abstractions_admissible {n : ℕ} (prob : STRIPS n) {V : Type} [FinEnum V]
    {g : NatGraph V} (abstraction : State' n → V)
    (is_abstraction : is_valid_abstraction (trans_of_STRIPS prob) g abstraction)
    (cost_le : ∀ (u v : State' n) (adj : (trans_of_STRIPS prob).Adj u v),
      NatGraph.edgeCost (is_abstraction u v adj) ≤ NatGraph.edgeCost adj) :
    heur_admissible' prob (fun s => abstraction_heuristic prob g abstraction s) := by
  intro v goal goal_in_goals path
  -- Map concrete walk to abstract walk
  let abstract_walk := map_walk_to_abstract abstraction is_abstraction path.val
  -- Abstract walk cost ≤ concrete walk cost
  have abstract_walk_cost_le := map_walk_cost_le abstraction is_abstraction cost_le path.val
  -- Get abstract path from walk
  obtain ⟨abstract_path, abstract_path_cost_le⟩ := WeightedDiGraph.Walk.cheaper_path_exists abstract_walk
  -- abstraction goal is in the mapped goals
  have goal_mapped : abstraction goal ∈ (trans_of_STRIPS_goals prob).map abstraction :=
    List.mem_map_of_mem (f := abstraction) goal_in_goals
  -- Unfold abstraction_heuristic and split on the match
  unfold abstraction_heuristic
  simp only
  split
  case h_1 h_none =>
    -- A* returned none, but we have an abstract path to abstraction goal which is in goals.map abstraction
    -- This contradicts completeness of A*
    have h_exists : ∃ g' ∈ (trans_of_STRIPS_goals prob).map abstraction,
        ∃ p : g.Path (abstraction v) g', p = p :=
      ⟨abstraction goal, goal_mapped, abstract_path, rfl⟩
    have h_some := NatGraph.astar_multigoal_is_complete (fun _ => 0) (abstraction v)
      ((trans_of_STRIPS_goals prob).map abstraction) h_exists
    rw [h_none] at h_some
    simp at h_some
  case h_2 ret h_some =>
    -- Need: ret.snd.val.cost ≤ path.cost
    -- Step 1: 0 heuristic is admissible for the abstract graph
    have zero_admissible : g.admissible' (fun _ => 0) ((trans_of_STRIPS_goals prob).map abstraction) := by
      intro v' goal' _; unfold NatGraph.cost_ge; intro p; exact Nat.zero_le _
    -- Step 2: A* returned some, so get the isSome proof
    have astar_isSome : Option.isSome (NatGraph.astar_multigoal (g := g)
        (fun _ => 0) (abstraction v) ((trans_of_STRIPS_goals prob).map abstraction)) := by
      rw [h_some]; simp
    -- Step 3: Get augmented A* path
    have h_aug_some := NatGraph.astar_multigoal_some_implies_astar_some
      (fun (_ : V) => 0) (abstraction v) ((trans_of_STRIPS_goals prob).map abstraction) astar_isSome
    obtain ⟨aug_path, h_aug_eq⟩ := Option.isSome_iff_exists.mp h_aug_some
    -- Step 4: aug_path is cheapest
    have aug_optimal : aug_path.is_cheapest := by
      have h := NatGraph.astar_is_optimal
        (g := g.add_artificial_goal ((trans_of_STRIPS_goals prob).map abstraction))
        (NatGraph.opt_heur (fun (_ : V) => 0)) (some (abstraction v)) none
        (NatGraph.opt_heur_admissible _ zero_admissible) h_aug_some
      rw [Option.get_of_eq_some h_aug_some h_aug_eq] at h; exact h
    -- Step 5: Lift abstract_path to augmented
    obtain ⟨aug_p, h_cost_eq⟩ := NatGraph.lift_path_to_augmented_cost
      (G := g) goal_mapped abstract_path
    -- Step 6: aug_path.cost ≤ abstract_path.cost
    have h_aug_le : aug_path.cost ≤ abstract_path.cost := calc
      aug_path.cost ≤ aug_p.cost := aug_optimal aug_p
      _ = abstract_path.cost := h_cost_eq
    -- Step 7: ret.2.cost ≤ aug_path.cost
    have h_ret_le := NatGraph.astar_multigoal_cost_le_aug
      (fun (_ : V) => 0) (abstraction v) ((trans_of_STRIPS_goals prob).map abstraction)
      astar_isSome aug_path h_aug_eq
    -- Convert h_ret_le to use ret instead of .get
    have h_get_eq : (NatGraph.astar_multigoal (g := g) (fun _ => 0) (abstraction v)
        ((trans_of_STRIPS_goals prob).map abstraction)).get astar_isSome = ret := by
      exact Option.get_of_eq_some astar_isSome h_some
    rw [h_get_eq] at h_ret_le
    -- Step 8: Chain inequalities
    show path.cost ≥ ret.snd.cost
    calc ret.snd.cost ≤ aug_path.cost := h_ret_le
      _ ≤ abstract_path.cost := h_aug_le
      _ ≤ abstract_walk.cost := abstract_path_cost_le
      _ ≤ path.cost := by
          rw [WeightedDiGraph.Path.cost_same]; exact abstract_walk_cost_le



----------------------- Pattern DataBase Heuristics

-- a pattern is a set of variable indices
abbrev pattern (n : ℕ) := Finset (Fin n)


def project_pattern (n : ℕ) (pat : pattern n) (v : {v : Fin n // v ∈ pat}) : Fin (pat.card) :=
  ⟨ ∑ v' ∈ pat, if v' < v then 1 else 0, by
    simp
    apply lt_of_le_of_ne
    · rw [Finset.card_filter_le_iff]
      intro s' s'_sub_pat pat_card_lt_s'card
      apply Finset.card_le_card at s'_sub_pat
      exact absurd (lt_of_lt_of_le pat_card_lt_s'card s'_sub_pat) (lt_irrefl _)
    · intro eq
      apply Finset.filter_card_eq at eq
      specialize eq v.val v.prop
      exact (lt_self_iff_false v).mp eq
    ⟩

lemma projeect_pattern_monotone {n : ℕ} (pat : pattern n) (u v : {x : Fin n // x ∈ pat}) (u_lt_v : u < v) : project_pattern n pat u < project_pattern n pat v := by
  unfold project_pattern
  simp only [Finset.sum_boole, Nat.cast_id, Fin.mk_lt_mk]
  apply Finset.card_lt_card
  apply Finset.ssubset_iff.mpr
  use u
  simp_all only [Finset.mem_filter, SetLike.coe_mem, lt_self_iff_false, and_false, not_false_eq_true, true_and]
  apply Finset.subset_iff.mpr
  intro x x_in
  simp at x_in
  cases x_in
  case h.inl x_eq_u =>
    simp_all only [Finset.mem_filter, SetLike.coe_mem, Subtype.coe_lt_coe, and_self]
  case h.inr conj =>
    simp_all only [Finset.mem_filter, true_and]
    apply lt_trans
    · exact conj.2
    · apply u_lt_v

--lemma project_pattern_injective {n : ℕ} (pat : pattern n) : Function.Injective (project_pattern n pat) := ...


def project_pattern_List {n : ℕ} (pat : pattern n) (l : List (Fin n)) : List (Fin pat.card) := l.filterMap (fun e =>
  if e_in_pat : e ∈ pat then
    some (project_pattern n pat ⟨e,e_in_pat⟩) else none)

def project_pattern_VarSet' {n : ℕ} (pat : pattern n) (vs : VarSet' n) : VarSet' (pat.card) := ⟨project_pattern_List pat vs.val, by
    obtain ⟨val, property⟩ := vs
    apply List.sortedLT_iff_pairwise.mpr
    apply List.sortedLT_iff_pairwise.mp at property
    unfold project_pattern_List
    apply List.pairwise_filterMap.mpr
    simp
    apply List.Pairwise.imp ; rotate_left
    · exact property
    · intro a b a_lt_b a_in_pat b_in_pat
      apply projeect_pattern_monotone
      apply Subtype.mk_lt_mk.mpr
      exact a_lt_b
    ⟩

def project_pattern_action {n : ℕ} (a : Action n) (pat : pattern n) : Action (pat.card) := Action.mk a.name
    (project_pattern_VarSet' pat a.pre')
    (project_pattern_VarSet' pat a.add')
    (project_pattern_VarSet' pat a.del')
    a.cost

def project_pattern_state {n : ℕ} (pat : pattern n) (s : State' n) : State' (pat.card) :=
  let v : VarSet' n := varset'_of_state' s
  let v' : VarSet' (pat.card) := project_pattern_VarSet' pat v
  state'_of_varset' v'


def project_pattern_STRIPS {n : ℕ} (prob : STRIPS n) (pat : pattern n) : STRIPS (pat.card) :=
  let namesList : List String := (List.finRange pat.card).map (fun i : Fin (pat.card) => prob.varNames.get ⟨i, by
    unfold pattern at pat
    apply lt_of_lt_of_le
    · exact i.prop
    · apply le_trans
      · apply Finset.card_le_univ
      · simp
    ⟩)
  let names : Vector String (Finset.card pat) := ⟨ namesList.toArray , by grind⟩
  let actions : Actions' (Finset.card pat) := prob.actions'.map (fun a =>
    project_pattern_action a pat)
  let init : State' (Finset.card pat) := project_pattern_state pat prob.init'
  let goal : VarSet' (Finset.card pat) := project_pattern_VarSet' pat prob.goal'
  STRIPS.mk names actions init goal



def pdb_heuristic {n : ℕ} (prob : STRIPS n) (pat : pattern n) (s : State' n) : ℕ :=
  let pdb_trans : NatGraph (State' (pat.card)) := trans_of_STRIPS (project_pattern_STRIPS prob pat)
  abstraction_heuristic prob pdb_trans (project_pattern_state pat) (s)

/-
If action `a` is applicable in state `v`, then its projection is applicable in the
    projected state.
-/
lemma project_pattern_state_satisfies_pre {n : ℕ} (pat : pattern n) (a : Action n)
    (v : State' n) (h : applicable' a v = true) :
    applicable' (project_pattern_action a pat) (project_pattern_state pat v) = true := by
      unfold applicable' project_pattern_action project_pattern_state at *;
      unfold project_pattern_VarSet';
      unfold project_pattern_List at *
      simp_all [satisfies']
      intro x hx
      split_ifs <;> simp_all [state'_of_varset']
      -- Since x is in the pattern and in the preconditions, and v[x] is true, the project_pattern should map x to true in the projected state.
      have h_proj_true : (List.map (fun i => decide (i ∈ List.filterMap (fun e => if e_in_pat : e ∈ pat then some (project_pattern n pat ⟨e, e_in_pat⟩) else none) (varset'_of_state' v).1)) (List.finRange (Finset.card pat)))[project_pattern n pat ⟨x, by assumption⟩] = true := by
        unfold varset'_of_state' at *; simp_all +decide [ List.mem_filterMap ] ;
        exact ⟨ x, h x hx, by assumption, rfl ⟩;
      -- By definition of `BitVec.ofBoolListLE`, the element at position `i` in the BitVec is the same as the element at position `i` in the original list.
      have h_bitvec_eq_list : ∀ (l : List Bool), ∀ (i : Fin l.length), (BitVec.ofBoolListLE l)[i] = l[i] := by
        grind +suggestions;
      convert h_bitvec_eq_list _ _ using 1;
      rotate_left;
      rotate_left;
      exact List.map ( fun i => decide ( i ∈ List.filterMap ( fun e => if e_in_pat : e ∈ pat then some ( project_pattern n pat ⟨ e, e_in_pat ⟩ ) else none ) ( varset'_of_state' v ).1 ) ) ( List.finRange ( Finset.card pat ) );
      exact ⟨ project_pattern n pat ⟨ x, by assumption ⟩, by simp +decide ⟩;
      · simp
        congr! 1
        · grind
        · simp +decide [ List.length_map, List.length_finRange ]
          congr! 1
        · grind
        · grind
      · grind

/-- `project_pattern_state` at a projected index checks whether the corresponding
    original variable is in the pattern and true in the state. -/
lemma project_pattern_state_getElem {n : ℕ} (pat : pattern n) (s : State' n) (i : Fin pat.card) :
    (project_pattern_state pat s)[i.val] =
      decide (i ∈ (project_pattern_VarSet' pat (varset'_of_state' s)).val) := by
  unfold project_pattern_state
  rw [state'_of_varset'_getElem]

/-- Membership in `project_pattern_VarSet'` iff there exists a variable in the pattern
    and in the original var-set that projects to the given index. -/
lemma mem_project_pattern_VarSet' {n : ℕ} (pat : pattern n) (vs : VarSet' n)
    (x : Fin pat.card) :
    x ∈ (project_pattern_VarSet' pat vs).val ↔
      ∃ j ∈ vs.val, ∃ hj : j ∈ pat, project_pattern n pat ⟨j, hj⟩ = x := by
  unfold project_pattern_VarSet' project_pattern_List
  simp [List.mem_filterMap]

/-
If `a` transforms `v` into `v'`, then the projected action transforms the projected
    states.
-/
lemma project_pattern_preserves_successor {n : ℕ} (pat : pattern n) (a : Action n)
    (v v' : State' n) (h_succ : is_successor' a v v' = true) :
    is_successor' (project_pattern_action a pat) (project_pattern_state pat v)
      (project_pattern_state pat v') = true := by
        unfold is_successor' at *;
        simp_all [ project_pattern_action, project_pattern_VarSet', project_pattern_state ];
        intro x;
        split_ifs <;> simp_all [ project_pattern_List ];
        · rw [ state'_of_varset'_getElem ];
          simp_all [ varset'_of_state' ];
          grind;
        · obtain ⟨ y, hy, hy', rfl ⟩ := ‹_›;
          simp_all [ state'_of_varset'_getElem, varset'_of_state'_mem ];
          intro x hx hx'; specialize h_succ x; split_ifs at h_succ <;> simp_all
          intro h; have := projeect_pattern_monotone pat ⟨ x, hx' ⟩ ⟨ y, hy' ⟩
          have := projeect_pattern_monotone pat ⟨ y, hy' ⟩ ⟨ x, hx' ⟩ ; simp_all
          exact ‹x ∉ a.del'.val› ( by simpa [ le_antisymm this ‹y ≤ x› ] using hy );
        · rw [ state'_of_varset'_getElem, state'_of_varset'_getElem ];
          simp [ List.mem_filterMap, varset'_of_state'_mem ];
          grind

/-- The projected action has the same cost as the original action. -/
lemma project_pattern_action_cost {n : ℕ} (a : Action n) (pat : pattern n) :
    (project_pattern_action a pat).cost = a.cost := by
  unfold project_pattern_action
  rfl

/-
The abstract edge cost in the projected graph is at most the concrete edge cost.
-/
lemma project_cost_le {n : ℕ} (prob : STRIPS n) (pat : pattern n)
    (u v : State' n) (adj : (trans_of_STRIPS prob).Adj u v)
    (val_abs : is_valid_abstraction (trans_of_STRIPS prob)
      (trans_of_STRIPS (project_pattern_STRIPS prob pat)) (project_pattern_state pat)) :
    NatGraph.edgeCost (val_abs u v adj) ≤ NatGraph.edgeCost adj := by
      obtain ⟨a, ha, h_price⟩ : ∃ a ∈ prob.actions', applicable' a u ∧ is_successor' a u v ∧ a.cost = cost_of prob u v (is_successor_state_of_trans_STRIPS_adj prob u v adj) := by
        have := min_cost_action_cost_eq_cost_of prob u v ( is_successor_state_of_trans_STRIPS_adj prob u v adj );
        exact ⟨ _, min_cost_action_in_prob prob u v ( is_successor_state_of_trans_STRIPS_adj prob u v adj ), successor_implies_applicable ( min_cost_action_creates_successor prob u v adj ), successor_implies_is_successor ( min_cost_action_creates_successor prob u v adj ), this ⟩;
      convert cost_of_le_action_cost ( project_pattern_STRIPS prob pat ) ( project_pattern_state pat u ) ( project_pattern_state pat v ) ( project_pattern_action a pat ) _ _ _ using 1;
      rotate_left;
      exact val_abs u v adj;
      · unfold project_pattern_STRIPS;
        simp_all only [List.mem_map]
        apply Exists.intro
        · apply And.intro
          on_goal 2 => { rfl }
          · simp_all only
      · exact project_pattern_state_satisfies_pre pat a u h_price.1;
      · grind +suggestions

lemma pdb_heurisitc_admissible {n : ℕ} (prob : STRIPS n) (pat : pattern n) :
    heur_admissible' prob (pdb_heuristic prob pat) := by
  have val_abs : is_valid_abstraction (trans_of_STRIPS prob)
      (trans_of_STRIPS (project_pattern_STRIPS prob pat)) (project_pattern_state pat) := by
    unfold is_valid_abstraction
    intro v v' adj_prop
    unfold trans_of_STRIPS at adj_prop ⊢
    simp at adj_prop ⊢
    obtain ⟨a, is_act, appli, successor⟩ := adj_prop
    use (project_pattern_action a pat)
    refine ⟨?_, ?_, ?_⟩
    · unfold project_pattern_STRIPS; simp; use a
    · exact project_pattern_state_satisfies_pre pat a v appli
    · exact project_pattern_preserves_successor pat a v v' successor
  exact abstractions_admissible prob (project_pattern_state pat) val_abs
    (fun u v adj => project_cost_le prob pat u v adj val_abs)
