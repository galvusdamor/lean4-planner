# PDDL front end: parser, lifted semantics and grounder

This directory contains a parser for PDDL domain and problem files, a formal semantics for
the *lifted* (schematic, un-grounded) representation, and a verified grounder
(`Grounding/`) that turns a lifted instance into a propositional planning task and, for
tasks without conditional effects, into the `STRIPS.PlanningTask` interface used by the
`planning` directory.  The grounding is proved to preserve the semantics: plans, plan costs
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
| `Ast.lean` | abstract syntax: terms, types, formulas, effects, actions, domains, problems |
| `Parser.lean` | `parseDomain`, `parseProblem`, `parseDomainOrProblem` |
| `Printer.lean` | printing the abstract syntax back to PDDL (used for round-trip testing) |
| `Semantics.lean` | the lifted semantics (states, satisfaction, effects, transitions, plans, costs) |
| `TypeHierarchy.lean` | executable decision procedure for the subtype relation, with soundness and completeness proofs |
| `Eval.lean` | executable evaluation of formulas, effects, costs and plans, proved to agree with the semantics |
| `WellFormed.lean` | static well-formedness checks (declared predicates/functions/types, arities, bound variables) |
| `Examples.lean` | a worked example: a parsed instance, a verified plan and its cost |
| `Grounding/Task.lean` | the intermediate grounded representation `GroundTask` and its semantics |
| `Grounding/Compile.lean` | the naive full grounder `groundInstance` |
| `Grounding/CompileCorrect.lean` | the proof that the formula and effect compilers preserve the semantics |
| `Grounding/Correct.lean` | the proof that grounding preserves plans, plan costs and solvability |
| `Grounding/Strips.lean` | translation of a conditional-effect-free ground task to `STRIPS.PlanningTask`, with the corresponding preservation proof |
| `Grounding/Positive.lean` | positive normal form: removing negative literals from a ground task, with the preservation proof |
| `Grounding/Match.lean` | matching action schemas against a set of atoms (used by the reachability grounder) |
| `Grounding/Reach.lean` | the delete-relaxation reachability grounder `groundReachable`, with its preservation proof |
| `Grounding/Solve.lean` | the end to end solver `solveOutcome`: grounding, STRIPS translation and the A* of `planning/`, proved sound (plans are plans) and complete (unsolvable means unsolvable) |
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
the `planning` library (`STRIPS.planner_heap_fast`, see `planning/PlannerHeap.lean`), run on
the STRIPS task produced by the verified translation of `Grounding/Strips.lean`.  The
pipeline of `PDDL.solveOutcome` is

1. the type hierarchy of the domain is checked (the solver does this itself, so the results
   below have no hypotheses);
2. the instance is grounded by the reachability grounder `groundReachable`;
3. the ground task is compiled to positive normal form (`GroundTask.toPositive`), which
   removes negative preconditions;
4. it is translated to `STRIPS.PlanningTask` (`GroundTask.toSTRIPS`);
5. `STRIPS.planner_heap_fast` searches it with the blind heuristic, i.e. as a uniform-cost
   search — any admissible heuristic of `planning/` can be plugged in instead
   (`GroundTask.solveStripsWith`);
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
  neither the `2 ^ n` states nor the list of all goal states is ever materialised.

What limits the front end is the search itself, which is blind: `blocks/probBLOCKS-5-0`
(optimal cost 12) takes about 17 s, and `probBLOCKS-6-0` does not finish within two minutes.
Better search algorithms and heuristics from `planning/` and `SearchAlgorithms` can be
plugged into `GroundTask.solveStripsWith` as they become available.

`SolveExamples.lean` runs the solver on the parsed example instances and proves that each
returned plan solves the corresponding instance, and that a blocks world problem asking for
`(and (on a b) (on b a))` is unsolvable.

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
grounder), report the size of its translation to `STRIPS.PlanningTask` (`--strips`) and
solve it with the verified planner (`--solve`):

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
