import planning.PlannerCached
import planning.H1
import planning.LMCutH1PCF
import planning.H1Fast
import planning.LMCutFast
import planning.LMCutRun
import planning.PlannerFast

import Strips.Parser


def pathToString {n : ℕ} {prob : STRIPS.PlanningTask n} {cur goal : STRIPS.State n}
    (path : STRIPS.PlanningTask.Path prob cur goal) : String := match path with
    | .empty _ => ""
    | .cons a _ _ _ π => "(" ++ a.name ++ ")\n" ++ pathToString π

/-- Run the planner on the STRIPS task in `dom`.

`heur` selects the heuristic (`h1`, `h1fast`, `h0`, `lmcut`, `lmcutfast`), `search` the search algorithm: `fast` (default, the fact-indexed transition system), `cached`
is the lazily-deleted heap with linear path reconstruction and a memoising heuristic, `lazy`
the same search without the heuristic cache, `heap` the eager heap.  All three are proved to
return the same plan.  `trace` is the progress-output interval (`0` = silent). -/
def runPlanner (dom : String) (heur : String) (search : String) (trace : ℕ) : IO Unit := do
    let ⟨n, prob⟩ ← STRIPS.readPlanningTask dom
    let h : BitVec n → ℕ∞ := match heur with
    | "h1" => fun s => STRIPS.h_1 prob s
    | "h1fast" => fun s => STRIPS.h_1_fast prob s
    | "lmcut" => fun s => STRIPS.lmcut prob s STRIPS.h1_pcf
    | "lmcutfast" => fun s => STRIPS.lmcut_fast prob s
    | "h0" => fun _ => 0
    | _ => fun _ => 0
    let result := match search with
    | "heap" => STRIPS.planner_heap_fast prob h
    | "fast" => STRIPS.planner_cached_fast prob h trace
    | "lazy" => STRIPS.planner_heap_lazy_fast prob h trace
    | "cached" => STRIPS.planner_cached prob h trace
    | _ => STRIPS.planner_cached_fast prob h trace
    match result with
    | some plan =>
      IO.println "Solution found!"
      IO.println (pathToString plan.path)
    | none   => IO.println "No solution found."


def main (args : List String) : IO Unit := do
  match args with
  | [] => IO.println "Usage: planner <path> [h1|h1fast|h0|lmcut|lmcutfast] [fast|cached|lazy|heap] [trace-every]"
  | path :: [] => runPlanner path "h1" "fast" 0
  | path :: heur :: [] => runPlanner path heur "fast" 0
  | path :: heur :: search :: [] => runPlanner path heur search 0
  | path :: heur :: search :: trace :: _ =>
      runPlanner path heur search (trace.toNat?.getD 0)
