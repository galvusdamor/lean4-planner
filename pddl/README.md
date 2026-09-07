# PDDL front end: parser, lifted semantics and grounder

This directory contains a parser for PDDL domain and problem files, a formal semantics for
the *lifted* (schematic, un-grounded) representation, and a verified grounder
(`Grounding/`) that turns a lifted instance into a propositional planning task and, after
compiling away conditional effects, negative conditions and disjunctive goals, into the
`STRIPS.PlanningTask` interface used by the `planning` directory.  The grounding is proved to preserve the semantics: plans, plan costs
and solvability of the ground task are exactly those of the lifted instance.

## Supported fragment

The syntax follows the BNF of PDDL 3.1 (Gerevini & Long).  Supported requirement flags:

| flag | supported |
| --- | --- |
| `:strips`, `:typing`, `:equality` | yes |
| `:negative-preconditions`, `:disjunctive-preconditions` | yes |
| `:existential-preconditions`, `:universal-preconditions`, `:quantified-preconditions` | yes |
| `:conditional-effects`, `:adl` | yes |
| `:action-costs` | yes (argument dependent, not state dependent) |
| `:fluents`, `:numeric-fluents` | no |
| `:durative-actions` and all temporal features | no |
| `:preferences`, `:constraints` | no |
| `:derived-predicates` | no |

Anything outside the fragment is *rejected with an error message* rather than silently
ignored.  Concretely, the parser rejects durative actions, derived predicates, constraints
and preferences, timed initial literals, numeric effects other than
`(increase (total-cost) …)`, numeric comparisons in preconditions, negative literals in
`:init`, and metrics other than `(:metric minimize (total-cost))`.

For action costs, the only numeric fluent is `total-cost`; a cost is an integer constant or
an application of a static function (one whose values are fixed in `:init`) to the
arguments of the action.  This is exactly the "action costs" fragment of IPC benchmarks.

## Files

| file | contents |
| --- | --- |
| `Sexp.lean` | tokeniser (comments, case folding) and s-expression reader |
| `SexpRoundTrip.lean` | the proof that the reader inverts the printer at the s-expression level (`parseSexp_toString`, `parseSexps_render`) |
| `Ast.lean` | abstract syntax: terms, types, formulas, effects, actions, domains, problems |
| `Parser.lean` | `parseDomain`, `parseProblem`, `parseDomainOrProblem` |
| `Printer.lean` | printing the abstract syntax back to PDDL (used for round-trip testing) |
| `Semantics.lean` | the lifted semantics (states, satisfaction, effects, transitions, plans, costs) |
| `TypeHierarchy.lean` | executable decision procedure for the subtype relation, with soundness and completeness proofs |
| `Eval.lean` | executable evaluation of formulas, effects, costs and plans, proved to agree with the semantics |
| `WellFormed.lean` | static well-formedness checks (declared predicates/functions/types, arities, bound variables) |
| `Examples.lean` | a worked example: a parsed instance, a verified plan and its cost |
| `PlanFile.lean` | reading and writing plan files, and the verified plan-file validator (`validatePlanText`) |
| `PlanFileExamples.lean` | a worked example: a plan file validated against a parsed instance |
| `Grounding/Task.lean` | the intermediate grounded representation `GroundTask` and its semantics |
| `Grounding/Compile.lean` | the naive full grounder `groundInstance` |
| `Grounding/CompileCorrect.lean` | the proof that the formula and effect compilers preserve the semantics |
| `Grounding/Correct.lean` | the proof that grounding preserves plans, plan costs and solvability |
| `Grounding/Strips.lean` | translation of a conditional-effect-free ground task to `STRIPS.PlanningTask`, with the corresponding preservation proof |
| `Grounding/Positive.lean` | positive normal form: removing negative literals from a ground task, with the preservation proof |
| `Grounding/Match.lean` | matching action schemas against a set of atoms (used by the reachability grounder) |
| `Grounding/Reach.lean` | the delete-relaxation reachability grounder `groundReachable`, with its preservation proof |
| `Grounding/Solve.lean` | the end to end solver `solveOutcome`: grounding, STRIPS translation and the A* of `planning/`, proved sound (plans are plans) and complete (unsolvable means unsolvable); `--trace=N` prints search progress |
| `Grounding/SolveHeur.lean` | the same solver with a chosen admissible heuristic (`PDDL.Heur`: blind, `h^max`, LM-cut), with the same soundness and completeness results |
| `Grounding/Examples.lean` | worked examples: two instances grounded, one of them translated to STRIPS |
| `SolveExamples.lean` | worked examples for the solver, including a provably unsolvable instance |
| `test/` | test instances and a script running the front end over them and over a benchmark collection |

## The semantics in one paragraph

A state is a set of ground atoms (`State := Set Atom`), with the closed world assumption.
`Formula.Holds I σ s f` is satisfaction of a goal description `f` in state `s` under the
variable assignment `σ`, where quantifiers range over the objects of the instance whose
declared type is a subtype of the quantifier's type (`Instance.HasType`), and the subtype
relation is the reflexive-transitive closure of the declared type edges
(`Domain.TypeLE`).  An effect determines an add set and a delete set in the current state
(`Effect.addSet`, `Effect.delSet`), evaluated recursively through conjunctions, universally
quantified effects and conditional effects; the successor state is
`(s \ del) ∪ add` (`Effect.apply`), so additions win over deletions.  A ground action is
applicable if its name resolves to a schema, its arguments are type-correct and its
precondition holds (`Instance.Applicable`); `Instance.Execution` chains transitions, and
`Instance.IsPlan` says a sequence of ground actions reaches a goal state from the initial
state.  `Instance.planCost` sums the `(increase (total-cost) …)` contributions of the
executed actions (each action costs `1` in domains that do not declare `total-cost`).

## Executable counterparts and what is proved

The declarative semantics is a `Prop` over `Set Atom` and hence not executable.  `Eval.lean`
defines Boolean/list-valued counterparts and proves them equivalent, under the (checkable)
hypothesis `Domain.typesWellFormedB` that the upward closure computation on the type graph
converges — which holds for every acyclic type hierarchy:

* `Formula.evalB_iff`: `evalB` decides `Formula.Holds`;
* `Effect.mem_addL_iff`, `Effect.mem_delL_iff`, `Effect.toState_applyB`: the executable
  effect application computes the semantic successor state;
* `Instance.applicableB_iff`, `Instance.executeB_sound`, `Instance.executeB_complete`;
* `Instance.validPlanB_iff`: the executable plan validator accepts exactly the plans, i.e.
  it is a *verified* plan validator for the lifted semantics;
* `Instance.effectCostB_eq`, `Instance.actionCostB_eq`, `Instance.planCostB_eq` for costs;
* `typeLEB_sound` / `typeLEB_complete` / `typeLEB_iff` for the subtype test itself.

All of these are proved without extra axioms.  The example instance in `Examples.lean` is
parsed from PDDL source text at elaboration time and its plan/cost statements are then
discharged by evaluation (`native_decide`).

## The grounder

`Grounding/Compile.lean` implements *naive full grounding*: for every action schema, every
type-correct tuple of objects is enumerated (`Instance.instantiations`), and the schema's
precondition, effect and cost are evaluated under that instantiation.  The result is a
`GroundTask` (`Grounding/Task.lean`): a list of ground operators, an initial state and a
goal, all expressed in terms of the *ground atoms of the very same instance*, so that a
state of the ground task literally is a state of the lifted semantics.  This is what makes
the correctness statements below free of any state translation.

A ground operator carries a precondition (a conjunction of literals), a list of *conditional* effects
(`CondEff`: a condition, an add list and a delete list), a cost, and the ground action it
came from (`GroundOp.action`), so a plan of the ground task can be read back as a plan of
the lifted instance.  Conditional effects are therefore supported by the intermediate
representation; only the translation to `STRIPS.PlanningTask` requires them to be absent.

What the compiler does with a lifted goal description (used for preconditions, effect
conditions and the goal):

* the result is a disjunctive normal form over ground literals: atoms become positive
  literals, `(and …)` distributes over the disjuncts, `(or …)` concatenates them, `(not …)`
  is pushed inwards, and quantifiers are expanded over the objects of their type;
* `(= t₁ t₂)` is decided statically — after instantiation both sides are objects — so the
  ubiquitous `(not (= ?x ?y))` is supported;
* a disjunctive precondition yields one operator per disjunct, so that operators keep a
  conjunctive precondition; negative literals are kept, since the closed world assumption
  makes them meaningful (and `Grounding/Positive.lean` compiles them away when a purely
  positive task is required, e.g. for the STRIPS interface);
* an instantiation whose precondition is statically false is dropped;
* `(increase (total-cost) …)` must not sit below a condition that cannot be decided
  statically, since operator costs are state independent.

### What is proved

All statements assume `Domain.typesWellFormedB`, the same checkable hypothesis as the
executable evaluator, and `groundInstance I = some T`:

* `groundFormula_holds`: a compiled condition holds in a state iff the lifted formula does;
* `groundEffect_spec`: the compiled conditional effects and cost describe the same add set,
  delete set and cost as the lifted effect, in every state;
* `groundOps_sound` / `groundOps_complete`: every ground operator is applicable exactly when
  its ground action is and has the same successor state and cost (`OpSound`), and every
  ground action that is applicable anywhere has such an operator;
* `groundInstance_isPlan_iff`: the plans of `T` are exactly the plans of `I` (via
  `GroundOp.action`), `groundInstance_planCost`: with the same cost, and
  `groundInstance_solvable_iff`: hence the same solvability.

`Grounding/Strips.lean` translates a ground task without conditional effects
(`GroundTask.Unconditional`, decided by `unconditionalB`) to `STRIPS.PlanningTask`: the
variables are the atoms `T.atoms`, so variable `i` stands for `T.atoms[i]`, and states
correspond by `GroundTask.encode`.  Applicability, successor states and the goal test agree
(`applicable_toAction_iff`, `encode_result`, `goalState_iff`), executions correspond to
paths in both directions (`path_of_execution`, `execution_of_path`), and hence
`groundInstance_strips_solvable_iff`: the translated STRIPS task is solvable exactly when
the lifted PDDL instance is.  Note that `STRIPS.Action` uses `ℕ` costs, so the integer
costs are transported with `Int.toNat`.

### The reachability grounder

Full grounding enumerates *all* type-correct tuples, which is exponential in the arity of
the schemas.  `Grounding/Reach.lean` therefore also provides `groundReachable`, the usual
delete-relaxation reachability grounder: starting from the initial state, only the
instantiations whose positive preconditions are contained in the current atom set are
generated (by matching, `Grounding/Match.lean`), their add effects are collected, and the
process is iterated to a fixpoint.  It satisfies the same correctness statements as full
grounding — `groundReachable_isPlan_iff`, `groundReachable_planCost`,
`groundReachable_solvable_iff` — the extra argument being that an operator that is not
reachable under the delete relaxation can never occur in an execution from the initial
state (`execution_subset_reach`).

## Searching: an end to end verified planner

`Grounding/Solve.lean` closes the chain *PDDL text → instance → ground task →
`STRIPS.PlanningTask` → plan*.  It contains no search of its own: the search is the A\* of
the `planning` library (`STRIPS.planner_heap_lazy_fast`, see `planning/PlannerHeapLazy.lean`
— A\* with a lazily deleted heap and linear-time path reconstruction), run on the STRIPS task
produced by the verified translation of `Grounding/Strips.lean`.  The
pipeline of `PDDL.solveOutcome` is

1. the type hierarchy of the domain is checked (the solver does this itself, so the results
   below have no hypotheses);
2. the instance is grounded by the reachability grounder `groundReachable`;
3. the ground task is compiled to positive normal form (`GroundTask.toPositive`), which
   removes negative preconditions;
4. it is translated to `STRIPS.PlanningTask` (`GroundTask.toSTRIPS`);
5. `STRIPS.planner_heap_lazy_fast` searches it with the blind heuristic, i.e. as a
   uniform-cost search — any admissible heuristic of `planning/` can be plugged in instead
   (`GroundTask.solveStripsWith`; with a heuristic that costs something to evaluate, use
   `STRIPS.planner_cached`, which memoises it and returns the same plan);
6. the path returned is read back as a list of ground operators
   (`GroundTask.opsOfPath`, correct by `GroundTask.opsOfPath_spec`) and then as a list of
   ground actions of the *lifted* instance.

Two results:

* `solveOutcome_isPlan`: every plan returned is a plan of the *lifted* instance, in the
  sense of `Instance.IsPlan`;
* `solveOutcome_unsolvable`: if the search exhausts the reachable state space, the lifted
  instance really has no plan (this uses that the blind heuristic is admissible and the
  completeness proof of the planner in `planning/`).

The third outcome `SolveOutcome.unknown` means the grounder ran out of fuel, or the ground
task is not expressible as a `STRIPS.PlanningTask` — it has conditional effects or a
disjunctive goal — or the instance is outside the grounder's fragment; nothing is claimed
then.

### Conditional effects, disjunctive goals, and the full solver

`STRIPS.PlanningTask` has unconditional operators and a conjunctive goal, so `solveOutcome`
gives up on ground tasks that have either.  Two further verified compilations remove that
restriction.

*Conditional effects* (`Grounding/Unconditional.lean`).  `GroundTask.toUnconditional`
replaces an operator by one unconditional operator per *trigger pattern* of its conditional
effects: for every subset of the effects there is an operator whose precondition contains
the conditions of the effects in the subset and, for each of the others, the negation of one
literal of its condition, and whose effect is the union of the effects in the subset
(`GroundOp.expandEffs`).  Patterns with an inconsistent condition are dropped, which is what
keeps the expansion manageable when the effect conditions share literals.  Proved:
`toUnconditional_unconditional` (the result really has no conditional effects),
`toUnconditional_isPlan` and `isPlan_of_toUnconditional_isPlan` (the plans of the two tasks
correspond operator by operator, with the same ground actions and the same cost), and
`toUnconditional_solvable_iff`.  The compilation introduces negative preconditions, so it
runs *before* the positive normal form; it does not introduce new atoms
(`mem_atoms_toUnconditional`), so `NegFresh` survives.  It is exponential in the number of
conditional effects of a single operator, which is unavoidable for this compilation.

*Disjunctive goals* (`Grounding/GoalSplit.lean`).  Instead of encoding the disjunction with
extra atoms and operators, the task is split: `GroundTask.goalClauseTask T c` keeps the
operators and the initial state of `T` and has the single goal clause `c`, and
`isPlan_iff_exists_clause` says that a plan of `T` is exactly a plan of one of these tasks.

*The full solver* (`Grounding/SolveFull.lean`).  `PDDL.solveOutcomeFull` grounds, expands
conditional effects, compiles to positive normal form, and runs the planner once per goal
clause, returning the cheapest plan found (`GroundTask.bestPlan`, at most as expensive as any
candidate by `bestPlan_le`).  It has the same two guarantees —
`solveOutcomeFull_isPlan` and `solveOutcomeFull_unsolvable` — and returns `unknown` only if
the type hierarchy is malformed, the grounder runs out of fuel, or the instance already uses
the reserved predicate name `¬` of the positive normal form.  This is what `pddlparse
--solve` uses; `--solve-strips` selects the older restricted route, which avoids the
expansion of conditional effects.

### Cost optimality

`Grounding/Optimal.lean` carries the optimality of the A\* search
(`STRIPS.planner_cached_fast_optimal`) along the whole chain.  The link that was missing is
the cost of a path: `planCost_opsOfPath` (the operator sequence read off a path costs exactly
what the path costs) and `exists_path_cost` (every execution gives a path of the same cost).
Both need the operator costs to be nonnegative (`GroundTask.NonnegCosts`), because
`STRIPS.Action` has natural number costs and the translation applies `Int.toNat`.  Together
with the cost preservation of the grounder, of the two compilations and of the goal split,
this gives

* `PDDL.solveOutcomeOptimal_optimal`: the plan returned is of minimal cost among *all* plans
  of the lifted PDDL instance,

next to the usual `PDDL.solveOutcomeOptimal_isPlan` and
`PDDL.solveOutcomeOptimal_unsolvable`.  `PDDL.solveOutcomeOptimal` is
`PDDL.solveOutcomeFull` plus the nonnegativity check, and is what `pddlparse --solve` runs;
`--solve-full` runs the variant without that check, which then makes no optimality claim.

`SolveFullExamples.lean` solves the conditional-effect instance and the instance with the
existentially quantified (hence disjunctive) goal that the restricted solver reports as
`unknown`, proves the returned plans to be plans of the lifted semantics, and proves that no
plan of the `transport-lite` instance (whose `drive` action costs the length of the road) is
cheaper than the plan found.  On
<https://github.com/aibasel/downward-benchmarks/>, `miconic-simpleadl/s1-0` (0.3 s, cost 4)
and `openstacks-sat08-adl/p01` (0.9 s) are now solved end to end, while they were `unknown`
before.  The expansion itself is cheap on the instances tried (`schedule/probschedule-2-0`:
49 operators become 134152 in 2.7 s; `citycar-sat14-adl/p3-2-2-0-1`: 1220 become 1820); what
the resulting task size then costs is the search, as usual.  The `--expand` option of the
front end reports these numbers.  Domains without conditional effects are not slowed down by
the extra steps: `blocks/probBLOCKS-4-0`, `gripper/prob01`, `miconic/s1-0` and
`visitall-opt11-strips/problem03-full` are still solved in about 0.15 s each.

### Performance

The whole pipeline is executable, and grounding and translating are fast.  Measured with
the `--strips` option of the front end (which parses, grounds with the reachability
grounder, compiles to positive normal form and builds the `STRIPS.PlanningTask`) on
instances of <https://github.com/aibasel/downward-benchmarks/>:

| instance | STRIPS task | time |
| --- | --- | --- |
| `blocks/probBLOCKS-17-0` | 682 variables, 612 actions | 0.10 s |
| `visitall-sat11-strips/problem16` | 1984 variables, 960 actions | 0.56 s |
| `miconic/s30-0` | 2160 variables, 3600 actions | 0.78 s |
| `scanalyzer-08-strips/p20` | 774 variables, 29160 actions | 1.7 s |
| `depot/p22` | 3322 variables, 22924 actions | 3.8 s |
| `satellite/p36-HC-pfile16` | 6599 variables, 430159 actions | 41 s |
| `logistics98/prob30` | 13132 variables, 43752 actions | 57 s |

Three implementation choices account for most of this:

* the atoms of the task are collected once and indexed through a hash map, so that a
  variable set is built by setting the bits of the atoms that occur in it rather than by
  testing every atom of the task (`GroundTask.toSTRIPSFast`, and `GroundTask.varSetOfFast`
  for the individual operators).  Both are installed with `@[csimp]` and *proved* equal to
  the definitions they replace, so every statement about `toSTRIPS` is untouched; without
  them, building the STRIPS task of `miconic/s30-0` alone takes minutes;
* the positive atoms of a precondition are joined in a *connected* order — always an atom
  with as many already bound variables as possible (`orderAtoms` of `Grounding/Match.lean`).
  Domains that encode types as unary predicates otherwise produce huge intermediate
  results: for `logistics98/prob30` the textual order builds over a million partial
  substitutions for a single schema, and grounding takes minutes instead of seconds.  Only
  `mem_orderAtoms` (the reordering produces atoms of the original list) is needed to keep
  the completeness proof of the matching;
* the search is driven by the goal *predicate* and by the successor *generator*, so that
  neither the `2 ^ n` states nor the list of all goal states is ever materialised;
* applicability and goal tests go through `STRIPS.satisfies'`, whose compiled
  implementation is the bit-parallel `STRIPS.satisfies'_fast` (`@[csimp]`, proved equal),
  instead of enumerating the variables of the condition.

With these, `--solve` on the same benchmark collection (blind search, so the plans are cost
optimal):

| instance | plan cost | time |
| --- | --- | --- |
| `miconic/s1-0` | 4 | 0.11 s |
| `visitall-opt11-strips/problem03-full` | 8 | 0.11 s |
| `blocks/probBLOCKS-5-0` | 12 | 0.18 s |
| `gripper/prob02` | 17 | 0.30 s |
| `blocks/probBLOCKS-6-0` | 12 | 0.34 s |
| `miconic/s5-0` | 17 | 1.7 s |
| `blocks/probBLOCKS-7-0` | 20 | 5.1 s |

What limits the front end is still the search — the state space grows exponentially with the
instance size.

### Choosing the heuristic

Any admissible heuristic of `planning/` can be plugged into `GroundTask.solveStripsWith`.
`Grounding/SolveHeur.lean` does this for the heuristics of the library and exposes them as a
data type `PDDL.Heur`:

| name | heuristic |
| --- | --- |
| `h0` | the blind heuristic (uniform cost search), the default |
| `h1` | the critical path heuristic `STRIPS.h_1` (`h^max`) |
| `h1fast` | the same values, computed by `STRIPS.h_1_fast` (`STRIPS.h_1_fast_eq`) |
| `lmcut` | `STRIPS.lmcut` with the `h^max`-maximiser precondition-choice function |
| `lmcutfast` | the same values, computed by `STRIPS.lmcut_fast` (`STRIPS.lmcut_fast_eq`) |

All of them are proved admissible (`PDDL.Heur.toFun_admissible`), so the solver
`PDDL.solveOutcomeWith` keeps both guarantees for every choice
(`PDDL.solveOutcomeWith_isPlan`, `PDDL.solveOutcomeWith_unsolvable`), and the plans it
returns are cost optimal.  With a non-trivial heuristic the search used is
`STRIPS.planner_cached_fast`, which memoises the heuristic — a heap operation costs
`O(log m)` evaluations, so without the cache the search spends essentially all of its time
re-evaluating it — and is proved to return the same plan as the reference planner
(`STRIPS.planner_cached_fast_eq_planner`).  On the command line:

```
.lake/build/bin/pddlparse --solve --heur=h1fast DOMAIN.pddl PROBLEM.pddl
```

Whether a heuristic pays off is a separate, empirical question; `bench/README.md` reports a
run over 409 problems of ten IPC domains.  In short: within a 30 s limit blind search solves
82 of them and `h^max` 76, the plan costs agree on every instance solved by both, and LM-cut
is at present too expensive per state to be useful.

`SolveExamples.lean` runs the solver on the parsed example instances and proves that each
returned plan solves the corresponding instance, and that a blocks world problem asking for
`(and (on a b) (on b a))` is unsolvable.

## Validating plan files

A plan produced by a planner is usually a text file with one ground action per line, e.g.

```
; cost = 2 (unit cost)
(pick-up a)
(stack a b)
```

`pddl/PlanFile.lean` reads such a file (`parsePlan`; comments, step numbers of the
`N: (action …)` format and duration annotations are ignored) and validates it against an
instance (`validatePlanText`).  What is proved:

* `validatePlanText_isPlan`: if the validator accepts, the actions in the file really are a
  plan of the *lifted* semantics (`Instance.IsPlan`);
* `validatePlanText_not_isPlan`: if it rejects, they really are not;
* `planCostText_eq`: the cost it reports is `Instance.planCost` of that plan;
* `parsePlan_printPlan`: printing a plan and reading it back gives the plan again, provided
  every name in it is a token the tokeniser reproduces (`planNamesOkB`).

On the command line:

```
.lake/build/bin/pddlparse --validate=PLAN.txt DOMAIN.pddl PROBLEM.pddl
```

which prints `VALID` with the cost, or `FAIL … INVALID`, and exits nonzero in the latter case.

## The reader inverts the printer

That parsing a printed file gives back what was printed has so far only been *tested*, by
round-tripping benchmark files (`--roundtrip`, see below).  `pddl/SexpRoundTrip.lean` proves
it at the s-expression level:

* `parseSexp_toString : parseSexp x.toString = .ok x`, and
* `parseSexps_render`: the same for a sequence of s-expressions separated by any whitespace
  character and followed by any trailing whitespace, i.e. for a printed file.

Both assume `AtomsOk x`: every atom of `x` is a name the tokeniser reproduces verbatim —
nonempty, lower case, and free of whitespace, parentheses and `;`.  Some such assumption is
necessary: an atom containing a space cannot survive tokenisation.  The corresponding
statement one level up (parsing a printed *domain* or *problem* gives the same abstract
syntax tree) is not proved; it is still covered by the round-trip test only.

## Testing the parser

The executable `pddlparse` parses files and can additionally round-trip them
(`--roundtrip`: parse, print, parse again, compare abstract syntax trees) and statically
check problems against their domain (`--check`):

```
lake build pddlparse
.lake/build/bin/pddlparse --roundtrip --check DOMAIN.pddl PROBLEM.pddl ...
pddl/test/run-tests.sh [PATH-TO-downward-benchmarks]
```

It can also ground a problem (`--ground` for full grounding, `--reach` for the reachability
grounder), report the size of the task after expanding conditional effects (`--expand`) and
of its translation to `STRIPS.PlanningTask` (`--strips`), and solve it with the verified
planner (`--solve`, or `--solve-strips` for the route that does not expand conditional
effects), and check a plan file against a problem (`--validate=PLAN.txt`):

```
.lake/build/bin/pddlparse --reach --strips DOMAIN.pddl PROBLEM.pddl
.lake/build/bin/pddlparse --solve DOMAIN.pddl PROBLEM.pddl
```

The front end was run over 3841 files of 127 domains of
<https://github.com/aibasel/downward-benchmarks/> (blocks, transport, miconic, visitall,
airport, depot, satellite, openstacks, miconic-fulladl, and many more, including the ADL
domains of IPC 2014/2018/2023).  3621 files parse *and* round-trip successfully (parse,
print, parse again gives an identical abstract syntax tree) and pass the static
well-formedness check against their domain.  The 220 failures are of exactly two kinds:

* the four domains using derived predicates (`philosophers`, `optical-telegraphs`,
  `psr-middle`, `psr-large`) are rejected with an explanatory error, as intended, and
  consequently their 196 problem files cannot be checked against a domain;
* the 20 `zenotravel` problems fail the well-formedness check because the `zenotravel`
  domain file writes `(aircraft?a)` without a space in the precondition of `refuel`, which
  is a genuine typo in that benchmark (the token becomes a predicate name that is never
  declared).
