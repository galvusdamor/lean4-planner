import SearchAlgorithms.AStar

/-!
# Compatibility shims for the list-based multi-goal A* interface

The generator-enabled version of `SearchAlgorithms` reworked the multi-goal A* interface: the
artificial-goal augmentation `NatGraph.add_artificial_goal` now takes a *goal predicate*
`is_goal : V → Prop` (rather than an explicit list of goals), and the helper lemmas about the
list-based `astar_multigoal` were replaced by predicate-based `astar_multigoal_aux` lemmas.
Heuristics are now `ℕ∞`-valued.

This file re-derives, for the list-based `astar_multigoal`, the two helper lemmas the STRIPS
planner development relies on, by specialising the predicate `is_goal := (· ∈ goals)`.  Since
`astar_multigoal heur start goals` is *definitionally* `astar_multigoal_aux heur start (· ∈ goals)`,
these are thin wrappers.
-/

namespace NatGraph

open WeightedDiGraph

variable {V : Type} [FinEnum V] {g : NatGraph V}

/-- If list-based multi-goal A* returns a path, then the underlying single-goal A* on the
artificial-goal augmentation (with goal predicate membership in `goals`) also returns a path. -/
theorem astar_multigoal_some_implies_astar_some (heur : V → ℕ∞) (start : V) (goals : List V)
    (returned_path : Option.isSome (astar_multigoal (g := g) heur start goals)) :
    Option.isSome (astar (g := g.add_artificial_goal (· ∈ goals))
      (opt_heur heur) (some start) none) := by
  unfold astar_multigoal astar_multigoal_aux at returned_path
  cases h : astar (g := g.add_artificial_goal (· ∈ goals)) (opt_heur heur) (some start) none with
  | none => simp [h] at returned_path
  | some p => simp

/-- The cost of the path returned by list-based multi-goal A* is at most the cost of the
augmented single-goal A* path it is post-processed from. -/
theorem astar_multigoal_cost_le_aug (heur : V → ℕ∞) (start : V) (goals : List V)
    (returned_path : Option.isSome (astar_multigoal (g := g) heur start goals))
    (aug_path : (g.add_artificial_goal (· ∈ goals)).Path (some start) none)
    (h_eq : astar (g := g.add_artificial_goal (· ∈ goals))
      (opt_heur heur) (some start) none = some aug_path) :
    ((astar_multigoal (g := g) heur start goals).get returned_path).2.cost ≤ aug_path.cost :=
  astar_multigoal_aux_cost_le_aug heur start (· ∈ goals) returned_path aug_path h_eq

end NatGraph
