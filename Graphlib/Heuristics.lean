import Validator.PlanningTask.Core
import Validator.PlanningTask.Basic
import Graphlib.NatGraph
import Graphlib.Planning

import Mathlib.Logic.Lemmas

namespace Validator

abbrev heur_admissible {n : ℕ} (prob : STRIPS n) (heur : State' n → ℕ):=
  ∀ v : State' n, ∀ plan : Plan prob (convertState v), plan.path.cost ≥ (heur v)


abbrev heur_admissible' {n : ℕ} (prob : STRIPS n) (heur : State' n → ℕ):=
  ∀ v : State' n, ∀ goal ∈ trans_of_STRIPS_goals prob, ∀ path : WeightedDiGraph.Path (G:=trans_of_STRIPS prob) v goal, path.cost ≥ (heur v)

abbrev heur_goal_aware {n : ℕ} (prob : STRIPS n) (heur : State' n → ℕ) :=
  ∀ v : State' n, satisfies' prob.goal' v → (heur v = 0)

abbrev heur_consistent {n : ℕ} (prob : STRIPS n) (heur : State' n → ℕ) :=
  ∀ v : State' n, ∀ a ∈ prob.actions', applicable' a v → heur v ≤ heur (successor' a v) + a.cost

lemma admissible_of_admissible' {n : ℕ} (prob : STRIPS n) (heur : State' n → ℕ):
    heur_admissible' prob heur → heur_admissible prob heur := by
  intro h' v plan
  -- Get a BitVec representation of plan.last
  haveI : DecidablePred (Set.Mem plan.last) := last_dec prob v plan.last plan.path
  obtain ⟨g', hg'⟩ := state_has_bitvec plan.last
  -- Convert STRIPS path to graph walk
  obtain ⟨w, hw⟩ := strips_path_has_cheaper_walk prob (hg' ▸ plan.path)
  -- Get a graph Path from the walk
  obtain ⟨p, hp⟩ := WeightedDiGraph.Walk.cheaper_path_exists w
  -- Show g' is in the goals list
  have g'_in_goals : g' ∈ trans_of_STRIPS_goals prob := by
    rw [mem_trans_of_STRIPS_goals_iff]
    exact GoalState_implies_satisfies' prob g' (hg' ▸ plan.goal)
  -- Apply admissible'
  have hge := h' v g' g'_in_goals p
  -- Cost preservation under cast
  have hcost : (hg' ▸ plan.path).cost = plan.path.cost :=
    Path.cost_eq_of_cast hg' plan.path
  calc heur v ≤ p.cost := hge
    _ ≤ w.cost := hp
    _ ≤ (hg' ▸ plan.path).cost := hw
    _ = plan.path.cost := hcost

lemma admissible'_of_admissible {n : ℕ} (prob : STRIPS n) (heur : State' n → ℕ):
    heur_admissible prob heur → heur_admissible' prob heur := by
  intro h v goal goal_in_goals graphPath
  -- goal satisfies the goal condition
  have sat : satisfies' prob.goal' goal = true :=
    (mem_trans_of_STRIPS_goals_iff prob goal).mp goal_in_goals
  -- Convert graph path to STRIPS path
  let stripsPath := walk_to_strips_path prob graphPath.val sat
  -- Build a Plan
  have goal_sat := satisfies'_implies_GoalState prob goal sat
  let plan : Plan prob (convertState v) :=
    Plan.mk (convertState goal) stripsPath goal_sat
  -- Apply admissible
  have hplan := h v plan
  -- The costs are equal
  have cost_eq : plan.path.cost = graphPath.cost := by
    show stripsPath.cost = graphPath.cost
    rw [walk_to_strips_path_cost_eq, WeightedDiGraph.Path.cost_same]
  exact cost_eq ▸ hplan

/-
PROVIDED SOLUTION
h2 s ≤ h1 s (by dominated) ≤ path.cost (by admissible). Unfold heur_admissible' and use le_trans with dominated and admissible.
-/
lemma admissible_of_dominated_by_admissible {n : ℕ} (prob : STRIPS n) (h1 h2 : State' n → ℕ) (admissible : heur_admissible' prob h1) (dominated : ∀ s : State' n, h1 s ≥ h2 s) : heur_admissible' prob h2 := by
  intro v goal goal_in_goals p
  exact le_trans (dominated v) (admissible v goal goal_in_goals p)

private lemma strips_path_cost_ge_heur {n : ℕ} (prob : STRIPS n) (h : State' n → ℕ)
    (ga : heur_goal_aware prob h) (hc : heur_consistent prob h)
    (k : ℕ) {start : State' n} {goal : State n}
    (path : Path prob (convertState start) goal)
    (hlen : path.length ≤ k)
    (goal_state : prob.GoalState goal) :
    path.cost ≥ h start := by
  induction k generalizing start goal with
  | zero =>
    generalize hs : convertState start = s at path
    cases path with
    | empty =>
      simp [Path.cost]
      exact ga start (GoalState_implies_satisfies' prob start (hs ▸ goal_state))
    | cons => simp [Path.length] at hlen
  | succ k ih =>
    generalize hs : convertState start = s at path
    cases path with
    | empty =>
      simp [Path.cost]
      exact ga start (GoalState_implies_satisfies' prob start (hs ▸ goal_state))
    | cons a s2 ha succ path' =>
      subst hs
      haveI := successor_dec a (convertState start) s2 succ
      obtain ⟨s2', rfl⟩ := state_has_bitvec s2
      have a_app : applicable' a start = true := successor_implies_applicable succ
      have s2'_eq : s2' = successor' a start :=
        is_successor'_eq_successor' a start s2' (successor_implies_is_successor succ)
      subst s2'_eq
      have ih' := ih path' (by simp [Path.length] at hlen; exact hlen) goal_state
      calc h start ≤ h (successor' a start) + a.cost := hc start a (mem_actions'_of_mem_actions ha) a_app
        _ ≤ path'.cost + a.cost := Nat.add_le_add_right ih' _
        _ = (Path.cons a (convertState (successor' a start)) ha succ path').cost := by simp [Path.cost]
lemma heur_admissible_of_goal_aware_and_consistent {n : ℕ} (prob : STRIPS n) (h : State' n → ℕ):
    heur_goal_aware prob h ∧ heur_consistent prob h → heur_admissible prob h := by
  intro ⟨ga, hc⟩ v plan
  exact strips_path_cost_ge_heur prob h ga hc plan.path.length plan.path (le_refl _) plan.goal



------------------------------- Particular Heuristics

lemma zero_heur_admissible' {n : ℕ} (prob : STRIPS n) : heur_admissible' prob (fun _ => 0) := by
  exact fun v goal h => fun p => Nat.zero_le _

lemma zero_heur_admissible {n : ℕ} (prob : STRIPS n) : heur_admissible prob (fun _ => 0) := by
  apply admissible_of_admissible' prob
  apply zero_heur_admissible'


