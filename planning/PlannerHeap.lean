import SearchAlgorithms.MultigoalHeap
import planning.PlannerGen

/-!
# The STRIPS planner with a heap as search queue

`STRIPS.planner_heap_fast` is the STRIPS planner of `planning.Planner` run with the
*fastest* multi-goal A\* currently offered by `SearchAlgorithms`:

* the state space is explored through the successor *generator* of
  `STRIPS.trans_of_STRIPS_gen` (so the adjacency relation is never tested against all `2 ^ n`
  states),
* the goal test is the *predicate* `fun s => satisfies' prob.goal' s` (so the list of all goal
  states is never materialised — this is what `STRIPS.planner_gen_fast` already does), and
* the open list is the leftist heap of `SearchAlgorithms.HeuristicSearchHeap` instead of a
  sorted list.

Since `NatGraph.astar_multigoal_heap` is proved in `SearchAlgorithms` to return literally the
same result as the generator based `NatGraph.astar_multigoal_gen`, the planner returns exactly
the same plan as `STRIPS.planner_gen_fast`, and hence as the reference planner
`STRIPS.planner` (`STRIPS.planner_heap_fast_eq`, `STRIPS.planner_heap_fast_eq_planner`).  All
correctness statements therefore transfer: completeness
(`STRIPS.planner_heap_fast_complete`) and optimality (`STRIPS.planner_heap_fast_optimal`).

This is the entry point that the PDDL front end (`pddl.Grounding.Solve`) uses.  When better
search algorithms become available in `SearchAlgorithms`, only this file needs to change.
-/

namespace STRIPS

open NatGraph

variable {n : ℕ}

/-- **The STRIPS planner**: multi-goal A\* with a heap search queue on the generator based
transition system, driven by the goal predicate `satisfies' prob.goal'`, post-processed into a
STRIPS plan by `STRIPS.plan_of_gen_result`. -/
def planner_heap_fast (prob : PlanningTask n) (heur : BitVec n → ℕ∞) :
    Option (PlanningTask.Plan prob prob.init) :=
  plan_of_gen_result prob (fun s => satisfies' prob.goal' s = true) (fun _ h => h)
    (NatGraph.astar_multigoal_heap (trans_of_STRIPS_gen prob) heur
      (state'_of_varset' prob.init') (fun s => satisfies' prob.goal' s = true))

/-- The heap based planner returns exactly the same plan as the generator based
`planner_gen_fast`. -/
theorem planner_heap_fast_eq (prob : PlanningTask n) (heur : BitVec n → ℕ∞) :
    planner_heap_fast prob heur = planner_gen_fast prob heur := by
  unfold planner_heap_fast planner_gen_fast
  rw [NatGraph.astar_multigoal_heap_eq_gen]

/-- The heap based planner returns exactly the same plan as the reference planner
`STRIPS.planner`. -/
theorem planner_heap_fast_eq_planner (prob : PlanningTask n) (heur : BitVec n → ℕ∞) :
    planner_heap_fast prob heur = planner prob heur := by
  rw [planner_heap_fast_eq, planner_gen_fast_eq, planner_gen_eq]

/-- **Completeness**: if the planner returns no plan, the task is unsolvable. -/
theorem planner_heap_fast_complete (prob : PlanningTask n) (heur : BitVec n → ℕ∞)
    (admissible : heur_admissible' prob heur) :
    planner_heap_fast prob heur = Option.none → PlanningTask.Unsolvable prob := by
  rw [planner_heap_fast_eq]
  exact planner_gen_fast_complete prob heur admissible

/-- **Optimality**: the returned plan is at least as cheap as every plan of the task. -/
theorem planner_heap_fast_optimal (prob : PlanningTask n) (heur : BitVec n → ℕ∞)
    (admissible : heur_admissible prob heur)
    (ret_plan : (planner_heap_fast prob heur).isSome) :
    ∀ plan : PlanningTask.Plan prob prob.init,
      plan.path.cost ≥ ((planner_heap_fast prob heur).get ret_plan).path.cost := by
  revert ret_plan
  rw [planner_heap_fast_eq]
  intro ret_plan
  exact planner_gen_fast_optimal prob heur admissible ret_plan

end STRIPS
