import SearchAlgorithms.AStarCached
import planning.PlannerHeapLazy

/-!
# The STRIPS planner with a cached heuristic

`STRIPS.planner_cached` is the planner of `planning.PlannerHeapLazy` — multi-goal A\* on the
successor generator, with a lazily deleted heap and linear-time path reconstruction — run with
a **memoising** heuristic.

A heuristic is a pure function of the state, but a search calls it very often: once per
neighbour of every expanded state (the test `heur v ≠ ⊤`) and twice per comparison inside the
queue.  With an expensive heuristic such as `STRIPS.h_1` that dominates the run time.
`SearchAlgorithms.CachedHeuristic` evaluates `heur v` at most once per state; since it carries
the proof that it *is* `heur` (`CachedFun.fn_eq`), the cached search is literally the uncached
one and every correctness statement transfers.

The cache is indexed by `STRIPS.bitVecVIndex`, which numbers a state by the value of its bit
vector.  These numbers are as large as `2 ^ n`, so the cache must be one that only allocates
what it touches: `CachedFun.ofWTrie`, the lazily built 16-way trie, with enough levels to
cover `n` bits.  (A state whose number does not fit simply misses the cache and is
recomputed, so the depth never affects the result — only the run time.)
-/

namespace STRIPS

open NatGraph SearchAlgorithms

variable {n : ℕ}

/-- The vertex numbering used to index the heuristic cache: a state is numbered by the value
of its bit vector. -/
def bitVecVIndex (n : ℕ) : VIndex (BitVec n) where
  idx v := v.toNat
  ofIdx m := if h : m < 2 ^ n then some (BitVec.ofNatLT m h) else none
  ofIdx_idx v := by
    simp only [dif_pos v.isLt]
    simp

/-- The number of levels of the 16-way trie needed for `n`-bit state numbers. -/
def trieDepth (n : ℕ) : ℕ := n / 4 + 1

/-- The memoising version of a heuristic on states: `heur` is evaluated at most once per
state, and never for a state the search does not look at. -/
def cachedHeur (heur : BitVec n → ℕ∞) : CachedHeuristic (BitVec n) heur :=
  CachedFun.ofWTrie (bitVecVIndex n) (trieDepth n) heur

/-- **The STRIPS planner with a cached heuristic**: `planner_heap_lazy_fast` run with
`cachedHeur heur` instead of `heur`. -/
def planner_cached (prob : PlanningTask n) (heur : BitVec n → ℕ∞) (te : ℕ := 0) :
    Option (PlanningTask.Plan prob prob.init) :=
  plan_of_gen_result prob (fun s => satisfies' prob.goal' s = true) (fun _ h => h)
    (NatGraph.astar_multigoal_heap_lazy_fastpath_cached (trans_of_STRIPS_gen prob)
      (cachedHeur heur) (state'_of_varset' prob.init')
      (fun s => satisfies' prob.goal' s = true) te)

/-- Caching the heuristic changes nothing: the cached planner returns the same plan as
`planner_heap_lazy_fast`. -/
theorem planner_cached_eq_lazy (prob : PlanningTask n) (heur : BitVec n → ℕ∞) (te : ℕ) :
    planner_cached prob heur te = planner_heap_lazy_fast prob heur te := by
  unfold planner_cached planner_heap_lazy_fast
  rw [NatGraph.astar_multigoal_heap_lazy_fastpath_cached_eq,
    NatGraph.astar_multigoal_heap_lazy_fastpath_eq]

/-- The cached planner returns exactly the same plan as the generator based
`planner_gen_fast`. -/
theorem planner_cached_eq (prob : PlanningTask n) (heur : BitVec n → ℕ∞) (te : ℕ) :
    planner_cached prob heur te = planner_gen_fast prob heur := by
  rw [planner_cached_eq_lazy, planner_heap_lazy_fast_eq]

/-- The cached planner returns exactly the same plan as the reference planner
`STRIPS.planner`. -/
theorem planner_cached_eq_planner (prob : PlanningTask n) (heur : BitVec n → ℕ∞) (te : ℕ) :
    planner_cached prob heur te = planner prob heur := by
  rw [planner_cached_eq_lazy, planner_heap_lazy_fast_eq_planner]

/-- **Completeness**: if the planner returns no plan, the task is unsolvable. -/
theorem planner_cached_complete (prob : PlanningTask n) (heur : BitVec n → ℕ∞) (te : ℕ)
    (admissible : heur_admissible' prob heur) :
    planner_cached prob heur te = Option.none → PlanningTask.Unsolvable prob := by
  rw [planner_cached_eq_lazy]
  exact planner_heap_lazy_fast_complete prob heur te admissible

/-- **Optimality**: the returned plan is at least as cheap as every plan of the task. -/
theorem planner_cached_optimal (prob : PlanningTask n) (heur : BitVec n → ℕ∞) (te : ℕ)
    (admissible : heur_admissible prob heur)
    (ret_plan : (planner_cached prob heur te).isSome) :
    ∀ plan : PlanningTask.Plan prob prob.init,
      plan.path.cost ≥ ((planner_cached prob heur te).get ret_plan).path.cost := by
  revert ret_plan
  rw [planner_cached_eq_lazy]
  intro ret_plan
  exact planner_heap_lazy_fast_optimal prob heur te admissible ret_plan

end STRIPS
