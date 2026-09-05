import planning.PlannerCached
import planning.SuccIndex

/-!
# The STRIPS planner with the fact-indexed transition system

`STRIPS.planner_cached` runs the A\* of `SearchAlgorithms` on `STRIPS.trans_of_STRIPS_gen`.
That transition system computes the cost of an edge `f → t` with `STRIPS.cost_of`, which
scans **all** actions of the task; since the search asks for the cost of every generated
edge, one state expansion costs `k + 1` full action scans for a branching factor of `k`.

`STRIPS.planner_cached_fast` runs exactly the same search on `STRIPS.trans_of_STRIPS_gen_fast`,
whose edge costs are computed with `STRIPS.cost_of_fast`: the fact index of the task
(`STRIPS.mkFactIndex`, see `planning.SuccIndex`) is built **once**, when the transition system
is created, and the cost of an edge only examines the actions that add (or delete) a fact on
which the two states differ.

The two transition systems are *equal* (`STRIPS.trans_of_STRIPS_gen_fast_eq`) — same
adjacency relation, same neighbour generator, and edge costs that agree by
`STRIPS.cost_of_fast_eq` — so the fast planner returns literally the same plan as
`STRIPS.planner_cached` and hence as the reference planner `STRIPS.planner`
(`STRIPS.planner_cached_fast_eq_planner`); completeness and optimality transfer.
-/

namespace STRIPS

open NatGraph SearchAlgorithms

variable {n : ℕ}

/-! ### The fact-indexed transition system -/

/-- The STRIPS transition system with edge costs computed through the fact index.  The index
is bound outside the record, so it is built once per transition system and shared by all edge
cost computations. -/
def trans_of_STRIPS_fast (prob : PlanningTask n) : NatGraph (BitVec n) :=
  let idx : {i : FactIndex n // i = mkFactIndex prob} := ⟨mkFactIndex prob, rfl⟩
  let edges : BitVec n → BitVec n → Prop := fun f t => is_successor_state prob f t
  let dg : Digraph (BitVec n) := Digraph.mk edges
  let dg_dec : DecidableRel dg.Adj := by infer_instance
  let cost : (u v : BitVec n) → dg.Adj u v → ℕ := fun f t adj =>
    cost_of_fast prob idx.1 idx.2 f t (by unfold is_successor_state; grind)
  WeightedDiGraph.mk dg cost dg_dec

/-- The fact-indexed transition system is the transition system. -/
theorem trans_of_STRIPS_fast_eq (prob : PlanningTask n) :
    trans_of_STRIPS_fast prob = trans_of_STRIPS prob := by
  unfold trans_of_STRIPS_fast trans_of_STRIPS
  simp only
  congr 1
  funext f t adj
  exact cost_of_fast_eq prob _ rfl f t _

/-- The generator based transition system with the fact-indexed edge costs. -/
def trans_of_STRIPS_gen_fast (prob : PlanningTask n) : NatGraphWithGenerator (BitVec n) where
  toWeightedDiGraph := trans_of_STRIPS_fast prob
  neighbours := transGenNeighbours prob
  neighbours_are_adj := by
    intro u v
    rw [trans_of_STRIPS_fast_eq]
    show is_successor_state prob u v ↔ v ∈ transGenNeighbours prob u
    rw [mem_transGenNeighbours]
  neighbours_sublist := transGenNeighbours_sublist prob

/-- The fact-indexed generator transition system is the generator transition system. -/
theorem trans_of_STRIPS_gen_fast_eq (prob : PlanningTask n) :
    trans_of_STRIPS_gen_fast prob = trans_of_STRIPS_gen prob := by
  unfold trans_of_STRIPS_gen_fast trans_of_STRIPS_gen
  simp only
  congr 1
  exact trans_of_STRIPS_fast_eq prob

/-! ### The planner -/

/-- The cached planner, run on an arbitrary transition system that is *equal* to
`trans_of_STRIPS_gen prob`.  The equality is used to give the search result the type that
`plan_of_gen_result` expects; being an equality of proofs-free data, it is erased at run
time. -/
def planner_cached_on (prob : PlanningTask n) (G : NatGraphWithGenerator (BitVec n))
    (hG : G = trans_of_STRIPS_gen prob) (heur : BitVec n → ℕ∞) (te : ℕ := 0) :
    Option (PlanningTask.Plan prob prob.init) :=
  plan_of_gen_result prob (fun s => satisfies' prob.goal' s = true) (fun _ h => h)
    (hG ▸ NatGraph.astar_multigoal_heap_lazy_fastpath_cached G
      (cachedHeur heur) (state'_of_varset' prob.init')
      (fun s => satisfies' prob.goal' s = true) te)

/-- Running the search on an equal transition system changes nothing. -/
theorem planner_cached_on_eq (prob : PlanningTask n) (G : NatGraphWithGenerator (BitVec n))
    (hG : G = trans_of_STRIPS_gen prob) (heur : BitVec n → ℕ∞) (te : ℕ) :
    planner_cached_on prob G hG heur te = planner_cached prob heur te := by
  subst hG
  rfl

/-- **The STRIPS planner with the fact-indexed transition system.**  Same search, same plan
(`planner_cached_fast_eq`), but the cost of an edge is computed from the precomputed fact
index instead of by a scan of all actions. -/
def planner_cached_fast (prob : PlanningTask n) (heur : BitVec n → ℕ∞) (te : ℕ := 0) :
    Option (PlanningTask.Plan prob prob.init) :=
  planner_cached_on prob (trans_of_STRIPS_gen_fast prob) (trans_of_STRIPS_gen_fast_eq prob)
    heur te

/-- The fact-indexed planner returns the same plan as `planner_cached`. -/
theorem planner_cached_fast_eq (prob : PlanningTask n) (heur : BitVec n → ℕ∞) (te : ℕ) :
    planner_cached_fast prob heur te = planner_cached prob heur te :=
  planner_cached_on_eq prob _ _ heur te

/-- The fact-indexed planner returns the same plan as the reference planner `STRIPS.planner`. -/
theorem planner_cached_fast_eq_planner (prob : PlanningTask n) (heur : BitVec n → ℕ∞)
    (te : ℕ) : planner_cached_fast prob heur te = planner prob heur := by
  rw [planner_cached_fast_eq, planner_cached_eq_planner]

/-- **Completeness**: if the planner returns no plan, the task is unsolvable. -/
theorem planner_cached_fast_complete (prob : PlanningTask n) (heur : BitVec n → ℕ∞) (te : ℕ)
    (admissible : heur_admissible' prob heur) :
    planner_cached_fast prob heur te = Option.none → PlanningTask.Unsolvable prob := by
  rw [planner_cached_fast_eq]
  exact planner_cached_complete prob heur te admissible

/-- **Optimality**: the returned plan is at least as cheap as every plan of the task. -/
theorem planner_cached_fast_optimal (prob : PlanningTask n) (heur : BitVec n → ℕ∞) (te : ℕ)
    (admissible : heur_admissible prob heur)
    (ret_plan : (planner_cached_fast prob heur te).isSome) :
    ∀ plan : PlanningTask.Plan prob prob.init,
      plan.path.cost ≥ ((planner_cached_fast prob heur te).get ret_plan).path.cost := by
  revert ret_plan
  rw [planner_cached_fast_eq]
  intro ret_plan
  exact planner_cached_optimal prob heur te admissible ret_plan

end STRIPS
