-- This module serves as the root of the `Graphlib` library.
-- Import modules here that should be built as part of the library.
import Graphlib.Basic
import Graphlib.DFS2
import Graphlib.BFS
import Graphlib.AStar
import Graphlib.Dijkstra
import Graphlib.Planning
import Graphlib.Heuristics
import Graphlib.Planner
import Graphlib.AbstractionHeuristic
import Graphlib.DeleteRelaxation

import Validator.PlanningTask.Parser


def main (args : List String) : IO Unit := do
  match args with
  | [] => IO.println "Usage: myexe <path>"
  | path :: _ =>
    let ⟨_n, prob⟩ ← Validator.STRIPS.parse path -- What is `_n` here?
    match Validator.planner prob (fun _ => 0) with
    | some _ => IO.println "Solution found!"
    | none   => IO.println "No solution found."
