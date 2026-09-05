import SearchAlgorithms.AStarHeapLazyPath
import planning.PlannerHeap

/-!
# The STRIPS planner with a lazily deleted heap and linear path reconstruction

`STRIPS.planner_heap_lazy_fast` is the STRIPS planner of `planning.Planner` run with the
currently fastest multi-goal A\* of `SearchAlgorithms`:
`NatGraph.astar_multigoal_heap_lazy_fastpath`, i.e.

* the state space is explored through the successor *generator* of
  `STRIPS.trans_of_STRIPS_gen`,
* the goal test is the *predicate* `fun s => satisfies' prob.goal' s`,
* the open list is a leftist heap with **lazy deletion** (a decrease-key inserts a new entry
  instead of rebuilding the heap), and
* the plan is reconstructed from the mother pointers in **linear** time.

`SearchAlgorithms` proves that this search returns literally the same result as the reference
`astar_multigoal_aux`, so the planner returns exactly the same plan as `STRIPS.planner`
(`STRIPS.planner_heap_lazy_fast_eq_planner`), and completeness
(`STRIPS.planner_heap_lazy_fast_complete`) and optimality
(`STRIPS.planner_heap_lazy_fast_optimal`) transfer.

The extra argument `te` only controls the progress output of the search: if it is non-zero,
one line is printed on stderr every `te` expansions.  It is passed to `dbg_trace`, which is
the identity function, so it does not influence the result — as witnessed by the theorems
below, which hold for every `te`.
-/

namespace STRIPS

open NatGraph

variable {n : ℕ}

/-- **The STRIPS planner**: multi-goal A\* with a lazily deleted heap and linear-time path
reconstruction, on the generator based transition system, driven by the goal predicate
`satisfies' prob.goal'`, post-processed into a STRIPS plan by `STRIPS.plan_of_gen_result`. -/
def planner_heap_lazy_fast (prob : PlanningTask n) (heur : BitVec n → ℕ∞) (te : ℕ := 0) :
    Option (PlanningTask.Plan prob prob.init) :=
  plan_of_gen_result prob (fun s => satisfies' prob.goal' s = true) (fun _ h => h)
    (NatGraph.astar_multigoal_heap_lazy_fastpath (trans_of_STRIPS_gen prob) heur
      (state'_of_varset' prob.init') (fun s => satisfies' prob.goal' s = true) te)

/-- The lazy heap planner returns exactly the same plan as the generator based
`planner_gen_fast`. -/
theorem planner_heap_lazy_fast_eq (prob : PlanningTask n) (heur : BitVec n → ℕ∞) (te : ℕ) :
    planner_heap_lazy_fast prob heur te = planner_gen_fast prob heur := by
  unfold planner_heap_lazy_fast planner_gen_fast
  rw [NatGraph.astar_multigoal_heap_lazy_fastpath_eq, NatGraph.astar_multigoal_gen_eq]

/-- The lazy heap planner returns exactly the same plan as the reference planner
`STRIPS.planner`. -/
theorem planner_heap_lazy_fast_eq_planner (prob : PlanningTask n) (heur : BitVec n → ℕ∞)
    (te : ℕ) :
    planner_heap_lazy_fast prob heur te = planner prob heur := by
  rw [planner_heap_lazy_fast_eq, planner_gen_fast_eq, planner_gen_eq]

/-- **Completeness**: if the planner returns no plan, the task is unsolvable. -/
theorem planner_heap_lazy_fast_complete (prob : PlanningTask n) (heur : BitVec n → ℕ∞)
    (te : ℕ) (admissible : heur_admissible' prob heur) :
    planner_heap_lazy_fast prob heur te = Option.none → PlanningTask.Unsolvable prob := by
  rw [planner_heap_lazy_fast_eq]
  exact planner_gen_fast_complete prob heur admissible

/-- **Optimality**: the returned plan is at least as cheap as every plan of the task. -/
theorem planner_heap_lazy_fast_optimal (prob : PlanningTask n) (heur : BitVec n → ℕ∞) (te : ℕ)
    (admissible : heur_admissible prob heur)
    (ret_plan : (planner_heap_lazy_fast prob heur te).isSome) :
    ∀ plan : PlanningTask.Plan prob prob.init,
      plan.path.cost ≥ ((planner_heap_lazy_fast prob heur te).get ret_plan).path.cost := by
  revert ret_plan
  rw [planner_heap_lazy_fast_eq]
  intro ret_plan
  exact planner_gen_fast_optimal prob heur admissible ret_plan

/-- The lazy heap planner and the (eager) heap planner return the same plan. -/
theorem planner_heap_lazy_fast_eq_heap (prob : PlanningTask n) (heur : BitVec n → ℕ∞)
    (te : ℕ) :
    planner_heap_lazy_fast prob heur te = planner_heap_fast prob heur := by
  rw [planner_heap_lazy_fast_eq, planner_heap_fast_eq]

end STRIPS
