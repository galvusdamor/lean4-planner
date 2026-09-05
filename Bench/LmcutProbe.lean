import planning.LMCutFast
import planning.LMCutRun
import Strips.Parser
import pddl.Parser
import pddl.Grounding.Solve

/-!
Component-level profiling harness for the LM-cut heuristic (development aid).

Build with `lake build lmcutprobe` and run

```
.lake/build/bin/lmcutprobe [K | TASKFILE] ...
```

A numeric argument `K` profiles the components of one LM-cut evaluation on a chain task with
`K+1` variables, a non-numeric one on the initial state of the STRIPS task in that file.
A pair of `.pddl` files (domain first) is parsed, grounded and translated to a STRIPS task,
which is then profiled the same way.
-/

open STRIPS

/-- A chain task with `k+1` variables: init `{0}`, goal `{k}`, actions `i → i+1`. -/
def chainTask (k : ℕ) : PlanningTask (k + 1) where
  varNames := Vector.ofFn (fun i => s!"v{i}")
  actions' := (List.finRange k).map (fun i =>
    ⟨s!"a{i}", VarSet.ofList [⟨i.1, by omega⟩], VarSet.ofList [⟨i.1 + 1, by omega⟩],
      VarSet.ofList [], 1⟩)
  init' := VarSet.ofList [⟨0, by omega⟩]
  goal' := VarSet.ofList [⟨k, by omega⟩]

/-- Run `f` `reps` times and report the average in microseconds.  Note that the machine this
runs on can be noisy; compare components within one run, and repeat a run before believing a
small difference. -/
def timeRep (name : String) (reps : ℕ) (f : Unit → String) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let mut last := ""
  for _ in [0:reps] do
    last := f ()
    if last == "impossible" then IO.println "?"
  let t1 ← IO.monoNanosNow
  IO.println s!"{name}: {last} ({(t1 - t0) / (1000 * max reps 1)} us)"
  (← IO.getStdout).flush

def timeIt (name : String) (f : Unit → String) : IO Unit := timeRep name 1 f

/-- Time the components of one LM-cut evaluation of `p` at its initial state. -/
def probeTask {n : ℕ} (name : String) (p : PlanningTask n) : IO Unit := do
  let s := p.init'.toBitVec
  IO.println s!"--- {name}: vars = {n}, actions = {p.actions'.length}"
  timeIt "  h_1_fast     " (fun _ => toString (h_1_fast p s))
  timeRep "  lmcut_fast   " 20 (fun _ => toString ((lmcut_fast p s).getD 999))
  timeIt "  lmcut_fast x5" (fun _ =>
    toString (((List.range 5).map (fun _ => (lmcut_fast p s).getD 999)).sum))
  if hg : (set_init p s).goal'.toList = [] then
    IO.println "  (empty goal: no round to profile)"
  else
    let q := i_g_normal_form (set_init p s)
    have hp : has_preconditions q := i_g_normal_form_has_preconditions (set_init p s) hg
    -- the choice function as it is used by `lmcut_run`: built once, shared by every query
    let pcf := (h1_pcf_box q hp).fn
    let u_g := i_g_normalform_is_unitary_goal (set_init p s)
    let u_i := i_g_normalform_is_unitary_init (set_init p s)
    let jg := justification_graph q pcf
    timeRep "  h1Values     " 100 (fun _ => toString (h1Values q).toList.sum)
    timeRep "  h1Data       " 100 (fun _ => toString (h1Data q).length)
    timeRep "  h1 fixpoint  " 100 (fun _ =>
      toString (h1IterFixFast q (h1Data q) rfl (h_1_base (n + 2) q.init'.toBitVec)).toList.length)
    timeRep "  pcf-all      " 100 (fun _ =>
      toString ((q.actions'.attach.map (fun a => (pcf a).val.val)).sum))
    timeRep "  jgBuckets    " 100 (fun _ => toString ((jgBuckets q pcf).toList.map List.length).sum)
    timeRep "  jgAdd        " 100 (fun _ => toString (jgAdd q pcf).toList.length)
    timeRep "  univList     " 100 (fun _ =>
      toString (FinEnum.toList (Finset.univ : Finset (Fin (n + 2)))).length)
    timeRep "  goalZoneSet  " 100 (fun _ =>
      toString (goalZoneSet jg (get_unitary_goal q u_g)).length)
    timeRep "  goal_zone    " 100 (fun _ =>
      toString (goal_zone jg (get_unitary_goal q u_g)).length)
    timeRep "  cut          " 100 (fun _ =>
      toString (edges_entering_goal_zone jg (get_unitary_goal q u_g)).length)
    timeRep "  landmark     " 100 (fun _ =>
      toString (landmark_induced_by_cut q
        (edges_entering_goal_zone jg (get_unitary_goal q u_g)) pcf).length)
    timeRep "  lmcut_step   " 100 (fun _ => toString (lmcut_step q u_g pcf).2.1)
    timeRep "  reachable    " 100 (fun _ =>
      toString (reachable jg (get_unitary_init q u_i) (get_unitary_goal q u_g)))
    timeRep "  zero_reach   " 100 (fun _ =>
      toString (zero_cost_reachable jg (get_unitary_init q u_i) (get_unitary_goal q u_g)))
    timeRep "  closure-lm   " 100 (fun _ =>
      toString (get_all_equiv_delete_relaxed_actions q (lmcut_step q u_g pcf).1).length)
    timeRep "  landmark-bkts" 100 (fun _ =>
      toString (landmark_ofBuckets (jgBuckets q pcf)
        (cut_entering jg (goal_zone jg (get_unitary_goal q u_g)))).length)
    timeRep "  subprob-build" 100 (fun _ =>
      toString ((partition_STRIPS q (lmcut_step q u_g pcf).2.2 ⟨1, by omega⟩).actions'.map
        (fun a => a.cost)).sum)

/-- Parse a PDDL domain/problem pair, ground it and profile the resulting STRIPS task. -/
def probePddl (domFile probFile : String) : IO Unit := do
  let dc ← IO.FS.readFile domFile
  let pc ← IO.FS.readFile probFile
  match PDDL.parseDomain dc, PDDL.parseProblem pc with
  | .ok d, .ok p =>
    match PDDL.stripsTask ⟨d, p⟩ with
    | none => IO.println s!"{probFile}: not translatable to a STRIPS task"
    | some T => probeTask probFile T.toSTRIPS
  | .error e, _ => IO.println s!"{domFile}: {e}"
  | _, .error e => IO.println s!"{probFile}: {e}"

partial def probePairs : List String → IO Unit
  | d :: p :: rest => do probePddl d p; probePairs rest
  | _ => pure ()

def main (args : List String) : IO Unit := do
  let ks := args.filterMap (fun a => a.toNat?)
  let files := args.filter (fun a => a.toNat?.isNone)
  let pddls := files.filter (fun a => a.endsWith ".pddl")
  let others := files.filter (fun a => !a.endsWith ".pddl")
  for f in others do
    let ⟨_, p⟩ ← STRIPS.readPlanningTask f
    probeTask f p
  probePairs pddls
  let ks := if ks.isEmpty && files.isEmpty then [5, 10, 20] else ks
  for k in ks do
    probeTask s!"chain {k}" (chainTask k)
