import pddl.Parser
import pddl.Printer
import pddl.WellFormed
import pddl.Grounding.Positive
import pddl.Grounding.Reach
import pddl.Grounding.Solve

/-!
# A command line front end for the PDDL parser

Usage:

```
pddlparse [--roundtrip] [--print] [--check] [--ground] [--reach] [--strips] [--solve]
          DOMAIN.pddl PROBLEM.pddl ...
```

Each file is parsed as a PDDL domain or problem file (whichever it is) and a short summary
of the result, or the parse error, is printed.  With `--roundtrip`, the parsed abstract
syntax tree is additionally printed back to PDDL, parsed again, and the two trees are
compared; this checks that the parser does not silently lose information.  With `--print`,
the parsed abstract syntax tree is printed back to PDDL on standard output.  With `--check`,
every problem file is checked for static well-formedness against the domain file that
precedes it on the command line.  The exit code is
`0` if all files were processed successfully.  This is meant for testing the parser on
benchmark collections such as <https://github.com/aibasel/downward-benchmarks/>.

With `--ground`, every problem file is additionally grounded against the preceding domain
file (naive full grounding, see `pddl.Grounding.Compile`) and the size of the resulting
ground task is reported; if the task has negative conditions but no conditional effects, the
size of its positive normal form (see `pddl.Grounding.Positive`) is reported as well.  Note
that full grounding is exponential in the arity of the action schemas, so this can be slow
and memory hungry on large instances.  With `--reach`, the problem is grounded with the
delete-relaxation reachability grounder of `pddl.Grounding.Reach` instead, which only
instantiates the actions that can possibly become applicable and is usually far smaller and
faster.  With `--strips`, the ground task is additionally translated to the
`STRIPS.PlanningTask` interface of the `strips` library (through the positive normal form)
and the size of the resulting task is reported.  With `--solve`, every problem is finally
solved by the verified planner
`PDDL.solveOutcome` of `pddl.Grounding.Solve` (reachability grounding, positive normal form,
translation to `STRIPS.PlanningTask` and the A* search of the `planning` library) and the
plan is printed in IPC syntax.  By `PDDL.solveOutcome_isPlan` every plan printed this way is
guaranteed to be a plan of the lifted PDDL semantics, and by `PDDL.solveOutcome_unsolvable`
an instance reported as unsolvable really has no plan.  The search uses the blind heuristic,
so only small instances are solved in reasonable time.
-/

open PDDL

/-- A one line summary of a parsed domain. -/
def domainSummary (d : Domain) : String :=
  s!"domain {d.name}: {d.requirements.length} requirements, {d.types.length} type edges, " ++
  s!"{d.constants.length} constants, {d.predicates.length} predicates, " ++
  s!"{d.functions.length} functions, {d.actions.length} actions"

/-- A one line summary of a parsed problem. -/
def problemSummary (p : Problem) : String :=
  s!"problem {p.name} (domain {p.domain}): {p.objects.length} objects, " ++
  s!"{p.init.length} init elements, minimize-total-cost: {p.minimizeTotalCost}"

/-- Parse one file and report the outcome; if `roundtrip` is set, also check that printing
and re-parsing gives back the same abstract syntax tree.  Returns whether the file was
processed successfully, together with the parsed domain if the file was a domain file. -/
def parseFile (roundtrip : Bool) (echo : Bool) (check : Bool) (ground : Bool)
    (reach : Bool) (strips : Bool) (solve : Bool) (lastDomain : Option Domain)
    (path : String) : IO (Bool × Option Domain) := do
  let contents ← IO.FS.readFile path
  match parseDomainOrProblem contents with
  | .error e =>
    IO.println s!"FAIL {path}: {e}"
    return (false, none)
  | .ok (.dom d) =>
    if roundtrip then
      match parseDomain d.print with
      | .error e => IO.println s!"FAIL {path}: reparsing the printed domain failed: {e}"
                    return (false, none)
      | .ok d' =>
        if d' != d then
          IO.println s!"FAIL {path}: round trip changed the domain"
          return (false, none)
    if echo then IO.println d.print
    IO.println s!"OK   {path}: {domainSummary d}"
    return (true, some d)
  | .ok (.prob p) =>
    if roundtrip then
      match parseProblem p.print with
      | .error e => IO.println s!"FAIL {path}: reparsing the printed problem failed: {e}"
                    return (false, none)
      | .ok p' =>
        if p' != p then
          IO.println s!"FAIL {path}: round trip changed the problem"
          return (false, none)
    if echo then IO.println p.print
    if check then
      match lastDomain with
      | none => IO.println s!"FAIL {path}: no domain given for --check"
                return (false, none)
      | some d =>
        let errs := (Instance.mk d p).wfErrors
        if !errs.isEmpty then
          for e in errs do IO.println s!"FAIL {path}: {e}"
          return (false, none)
    IO.println s!"OK   {path}: {problemSummary p}"
    if ground then
      match lastDomain with
      | none =>
        IO.println s!"FAIL {path}: no domain given for --ground"
        return (false, lastDomain)
      | some d =>
        match groundInstance ⟨d, p⟩ with
        | none =>
          IO.println
            s!"     {path}: outside the propositionally expressible fragment, not grounded"
        | some T =>
          IO.println (s!"     {path}: grounded to {T.ops.length} operators over " ++
            s!"{T.atoms.length} atoms ({T.goal.length} goal clauses, " ++
            s!"unconditional: {T.unconditionalB}, positive: {T.positiveB})")
          if T.unconditionalB && T.negFreshB && !T.positiveB then
            let P := T.toPositive
            IO.println (s!"     {path}: positive normal form has {P.ops.length} " ++
              s!"operators over {P.atoms.length} atoms " ++
              s!"(STRIPS ready: {P.stripsReadyB})")
    if reach then
      match lastDomain with
      | none =>
        IO.println s!"FAIL {path}: no domain given for --reach"
        return (false, lastDomain)
      | some d =>
        match groundReachable ⟨d, p⟩ with
        | none =>
          IO.println
            s!"     {path}: not grounded (unsupported cost effect or fixpoint not reached)"
        | some T =>
          IO.println (s!"     {path}: reachability grounding: {T.ops.length} operators " ++
            s!"over {T.atoms.length} atoms ({T.goal.length} goal clauses, " ++
            s!"unconditional: {T.unconditionalB}, positive: {T.positiveB})")
    if strips then
      match lastDomain with
      | none =>
        IO.println s!"FAIL {path}: no domain given for --strips"
        return (false, lastDomain)
      | some d =>
        match stripsTask ⟨d, p⟩ with
        | none =>
          IO.println s!"     {path}: not translatable to STRIPS.PlanningTask"
        | some T =>
          let prob := T.toSTRIPS
          IO.println (s!"     {path}: STRIPS task with {T.numVars} variables and " ++
            s!"{prob.actions'.length} actions, " ++
            s!"{(prob.actions'.map (·.cost)).foldl max 0} maximal action cost")
    if solve then
      match lastDomain with
      | none =>
        IO.println s!"FAIL {path}: no domain given for --solve"
        return (false, lastDomain)
      | some d =>
        let I : Instance := ⟨d, p⟩
        match solveOutcome I with
        | .unknown =>
          IO.println s!"     {path}: no plan found (out of fuel or not expressible in STRIPS)"
        | .unsolvable => IO.println s!"     {path}: proved unsolvable"
        | .plan plan =>
          IO.println (s!"     {path}: plan of length {plan.length} " ++
            s!"(cost {I.planCostB plan}):")
          for a in plan do IO.println s!"{a}"
    return (true, lastDomain)

def main (args : List String) : IO UInt32 := do
  let roundtrip := args.contains "--roundtrip"
  let echo := args.contains "--print"
  let check := args.contains "--check"
  let ground := args.contains "--ground"
  let reach := args.contains "--reach"
  let strips := args.contains "--strips"
  let solve := args.contains "--solve"
  let files := args.filter (fun a => !a.startsWith "--")
  if files.isEmpty then
    IO.println
      ("usage: pddlparse [--roundtrip] [--print] [--check] [--ground] [--reach] " ++
        "[--strips] [--solve] FILE.pddl ...")
    return 1
  let mut ok := true
  let mut dom : Option Domain := none
  for p in files do
    let (r, d) ← parseFile roundtrip echo check ground reach strips solve dom p
    ok := ok && r
    if d.isSome then dom := d
  return if ok then 0 else 1
