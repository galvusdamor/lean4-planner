import Validator.PlanningTask.Core
import Validator.PlanningTask.Basic
import Graphlib.NatGraph
import Graphlib.Planning
import Graphlib.Heuristics

import Mathlib.Logic.Lemmas

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
--     := by sorry

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


