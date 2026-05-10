import Graphlib.Planner

import Validator.PlanningTask.Parser

def main (args : List String) : IO Unit := do
  match args with
  | [] => IO.println "Usage: myexe <path>"
  | path :: _ =>
    let ⟨_n, prob⟩ ← Validator.STRIPS.parse path -- What is `_n` here?
    match Validator.planner prob (fun _ => 0) with
    | some _ => IO.println "Solution found!"
    | none   => IO.println "No solution found."
