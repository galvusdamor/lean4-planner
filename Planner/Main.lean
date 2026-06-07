import planning.Planner
import planning.H1

import Validator.PlanningTask.Parser



def pathToString {n : ℕ} {prob : Validator.STRIPS n} {cur goal : Validator.State n} (path : Validator.Path prob cur goal) : String := match path with
    | .empty s => ""
    | .cons a _ _ _ π => "(" ++ a.name ++ ")\n" ++ (pathToString π)

def runPlanner (dom : String) (heur : String) : IO Unit := do
    let ⟨n, prob⟩ ← Validator.STRIPS.parse dom -- What is `_n` here?
    -- _n is the number of variables in the problem
    let h : (Validator.State' n → ℕ) := match heur with
    | "h1" => (fun s : Validator.State' n => Validator.h_1_new prob s)
    | "h0" => (fun _ => 0)
    | _ => (fun _ => 0)

    match Validator.planner prob h with
    | some plan =>
      IO.println "Solution found!"
      IO.println (pathToString plan.path)
    | none   => IO.println "No solution found."


def main (args : List String) : IO Unit := do
  match args with
  | [] => IO.println "Usage: myexe <path>"
  | path :: [] => runPlanner path "h1"
  | path :: heur :: _ => runPlanner path heur

