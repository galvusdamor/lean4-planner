import Validator.PlanningTask.Core
import Validator.PlanningTask.Basic
import Graphlib.NatGraph
import Graphlib.Planning
import Graphlib.Heuristics

import Mathlib.Logic.Lemmas

namespace Validator

-- P is the number of partitions
-- the partining assigns in each partition to each action a cost
abbrev cost_partitioning {n : ℕ} (prob : STRIPS n) (P : ℕ) := (p : Fin P) → (a : Fin prob.actions'.length) → ℕ

def is_valid_cost_partitioning {n : ℕ} (prob : STRIPS n) (P : ℕ) (partitioning : cost_partitioning prob P) :=
  ∀ a : Fin prob.actions'.length, ((List.finRange P).map (fun p => partitioning p a)).sum ≤ prob.actions'[a].cost

def partition_STRIPS {n P : ℕ} (prob : STRIPS n) (partitioning : cost_partitioning prob P) (p : Fin P) : STRIPS n :=
  let actions : Actions' n := prob.actions'.mapFinIdx (fun i a i_lt =>
    Action.mk a.name a.pre' a.add' a.del' (partitioning p ⟨i,i_lt⟩) )
  STRIPS.mk prob.varNames actions prob.init' prob.goal'


def partition_heuristics {n P : ℕ} (prob : STRIPS n) (partitioning : cost_partitioning prob P)
  (heurs : Fin P → STRIPS n → State' n → ℕ)
  (s : State' n) : ℕ :=
  ∑ p : Fin P, heurs p (partition_STRIPS prob partitioning p) s


-- proof idea: for any path in prob, each heurs p is admissible w.r.t. the reduced cost model
-- this means that heurs p returns less than the value of the path in that cost model
-- since we have a valid partitioning, if we add all the path costs in all partitions together, we can't get beyond the cost of the path
lemma partition_heuristics_admissible {n P : ℕ} (prob : STRIPS n) (partitioning : cost_partitioning prob P)
  (heurs : Fin P → STRIPS n → State' n → ℕ)
  (all_admissible : ∀ p : Fin P, heur_admissible' (partition_STRIPS prob partitioning p) (heurs p (partition_STRIPS prob partitioning p))):
    heur_admissible' prob (partition_heuristics prob partitioning heurs) := by sorry

