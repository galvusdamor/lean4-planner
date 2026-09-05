import planning.PlannerHeap
import planning.H1

import Strips.Parser


def pathToString {n : ℕ} {prob : STRIPS.PlanningTask n} {cur goal : STRIPS.State n}
    (path : STRIPS.PlanningTask.Path prob cur goal) : String := match path with
    | .empty _ => ""
    | .cons a _ _ _ π => "(" ++ a.name ++ ")\n" ++ pathToString π

def runPlanner (dom : String) (heur : String) : IO Unit := do
    let ⟨n, prob⟩ ← STRIPS.readPlanningTask dom
    let h : BitVec n → ℕ∞ := match heur with
    | "h1" => fun s => STRIPS.h_1 prob s
    | "h0" => fun _ => 0
    | _ => fun _ => 0
    match STRIPS.planner_heap_fast prob h with
    | some plan =>
      IO.println "Solution found!"
      IO.println (pathToString plan.path)
    | none   => IO.println "No solution found."


def main (args : List String) : IO Unit := do
  match args with
  | [] => IO.println "Usage: myexe <path>"
  | path :: [] => runPlanner path "h1"
  | path :: heur :: _ => runPlanner path heur

