import Graphlib.Planner
import Graphlib.H1

import Validator.PlanningTask.Parser

def main (args : List String) : IO Unit := do
  match args with
  | [] => IO.println "Usage: myexe <path>"
  | path :: _ =>
    let ⟨_n, prob⟩ ← Validator.STRIPS.parse path -- What is `_n` here?
    -- _n is the number of variables in the problem
    match Validator.planner prob (fun s => Validator.h_1_new prob s) with
    | some _ => IO.println "Solution found!"
    | none   => IO.println "No solution found."
