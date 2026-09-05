import pddl.Grounding.Solve
import pddl.Grounding.Examples

/-!
# Worked examples for the end to end solver

The verified solver `PDDL.solveChecked` (reachability grounding, positive normal form,
translation to `STRIPS.PlanningTask`, A\* of the `planning` library) is run on the example
instances of `pddl.Grounding.Examples`, which were obtained by parsing PDDL source text.  In
each case the plan it returns is *proved* to be a plan of the lifted PDDL semantics — the
proof is just an application of `PDDL.solveChecked_isPlan`, no further computation is
involved.  The only thing that has to be evaluated is that the solver returns the plan in
question.

The last section documents the current limitation of the ground pipeline: a ground task with
conditional effects is not a STRIPS task, and the solver answers `unknown`.
-/

namespace PDDL
namespace Examples

/-! ### The blocks world example -/

/-- The plan found by the solver for the blocks world instance. -/
def blocksSolution : List GroundAction := (solveChecked blocks 100).getD []

theorem blocks_solve : solveChecked blocks 100 = some blocksSolution := by
  native_decide

/-- The plan found by the solver really is a plan of the lifted instance. -/
theorem blocksSolution_isPlan : blocks.IsPlan blocksSolution :=
  solveChecked_isPlan blocks_solve

theorem blocksSolution_eq :
    blocksSolution = [⟨"pick-up", ["a"]⟩, ⟨"stack", ["a", "b"]⟩] := by
  native_decide

/-! ### The example with negative and disjunctive preconditions

Negative preconditions are removed by the positive normal form compilation, which the
pipeline applies before the STRIPS translation. -/

/-- The plan found by the solver for the robot instance. -/
def robotSolution : List GroundAction := (solveChecked robot 100).getD []

theorem robot_solve : solveChecked robot 100 = some robotSolution := by
  native_decide

/-- The plan found by the solver really is a plan of the lifted instance. -/
theorem robotSolution_isPlan : robot.IsPlan robotSolution :=
  solveChecked_isPlan robot_solve

theorem robotSolution_eq : robotSolution = [⟨"move", ["a", "b"]⟩, ⟨"tidy", ["b"]⟩] := by
  native_decide

/-! ### A provably unsolvable instance

The solver also *proves* unsolvability: if A\* exhausts the reachable state space of the
STRIPS task without finding a plan, the lifted instance has no plan at all
(`PDDL.solveOutcome_unsolvable`). -/

/-- A blocks world problem asking for two blocks to be stacked on each other, which is
impossible. -/
def blocksImpossibleProblemSrc : String :=
"(define (problem impossible)
 (:domain blocks)
 (:objects a b - block)
 (:init (ontable a) (ontable b) (clear a) (clear b) (handempty))
 (:goal (and (on a b) (on b a))))"

/-- The unsolvable blocks world instance. -/
def blocksImpossible : Instance :=
  ⟨blocks.domain,
   (parseProblem blocksImpossibleProblemSrc).toOption.getD (emptyProblem "parse-error")⟩

theorem blocksImpossible_solveOutcome :
    solveOutcome blocksImpossible 100 = .unsolvable := by
  native_decide

/-- The instance really has no plan. -/
theorem blocksImpossible_not_solvable : ¬ blocksImpossible.Solvable :=
  solveOutcome_unsolvable blocksImpossible_solveOutcome

/-! ### The limits of the ground pipeline

`STRIPS.PlanningTask` has unconditional operators and a conjunctive goal, so a ground task
with conditional effects (such as the one of the `transport-lite` instance, where `drive`
moves a package along if it is loaded) is outside its scope.  The solver detects this and
answers `unknown`, which claims nothing about the instance. -/

theorem transportLiteConj_solveOutcome :
    solveOutcome transportLiteConj 100 = .unknown := by
  native_decide

end Examples
end PDDL
