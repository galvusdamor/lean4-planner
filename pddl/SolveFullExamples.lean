import pddl.Grounding.SolveFull
import pddl.Grounding.Optimal
import pddl.SolveExamples

/-!
# Worked examples for the solver of the whole grounded fragment

`pddl.SolveExamples` runs the restricted solver `PDDL.solveChecked`, which gives up
(`unknown`) on ground tasks with conditional effects or a disjunctive goal.  Here the same
kind of examples are run through `PDDL.solveFullChecked`, which compiles both features away
first (`pddl.Grounding.Unconditional`, `pddl.Grounding.GoalSplit`).

The two instances used are exactly the ones the restricted solver could not handle:

* `transportLiteConj` has a conditional effect (`drive` takes the package along if it is
  loaded) — `PDDL.Examples.transportLiteConj_solveOutcome` shows that the restricted solver
  answers `unknown` on it;
* `transportLite` has, in addition, an existentially quantified goal, which the grounder
  expands into a goal with two disjuncts
  (`PDDL.Examples.transportLite_groundInstance_disjunctive_goal`).

In both cases the plan the solver returns is *proved* to be a plan of the lifted PDDL
semantics; the proof is an application of `PDDL.solveFullChecked_isPlan`, the only thing
evaluated being that the solver returns this plan.
-/

namespace PDDL
namespace Examples

/-! ### An instance with conditional effects -/

/-- The plan the full solver finds for the conditional-effect instance. -/
def transportLiteConjSolution : List GroundAction :=
  (solveFullChecked transportLiteConj .blind 100).getD []

theorem transportLiteConj_solveFull :
    solveFullChecked transportLiteConj .blind 100 = some transportLiteConjSolution := by
  native_decide

/-- **The plan really is a plan of the lifted instance**, conditional effects and all. -/
theorem transportLiteConjSolution_isPlan :
    transportLiteConj.IsPlan transportLiteConjSolution :=
  solveFullChecked_isPlan transportLiteConj_solveFull

theorem transportLiteConjSolution_eq :
    transportLiteConjSolution =
      [⟨"load", ["truck", "pkg", "loc1"]⟩, ⟨"drive", ["truck", "loc1", "loc2"]⟩] := by
  native_decide

/-! ### An instance with conditional effects and a disjunctive goal -/

/-- The plan the full solver finds for the instance with the existentially quantified
goal. -/
def transportLiteSolution : List GroundAction :=
  (solveFullChecked transportLite .blind 100).getD []

theorem transportLite_solveFull :
    solveFullChecked transportLite .blind 100 = some transportLiteSolution := by
  native_decide

/-- **The plan really is a plan of the lifted instance**, disjunctive goal and all. -/
theorem transportLiteSolution_isPlan : transportLite.IsPlan transportLiteSolution :=
  solveFullChecked_isPlan transportLite_solveFull

/-! ### A plan that is proved to be a cheapest one

`PDDL.solveOutcomeOptimal` additionally checks that the action costs are nonnegative, and
then the plan it returns is of minimal cost among *all* plans of the lifted instance
(`PDDL.solveOutcomeOptimal_optimal`).  The `transport-lite` instance has argument-dependent
action costs (driving costs the length of the road), so this says something: no plan of it
is cheaper than the one below. -/

/-- The plan the optimal solver finds for the conditional-effect instance. -/
def transportLiteConjOptimal : List GroundAction :=
  match solveOutcomeOptimal transportLiteConj .blind 100 with
  | .plan σ => σ
  | _ => []

theorem transportLiteConj_solveOptimal :
    solveOutcomeOptimal transportLiteConj .blind 100 = .plan transportLiteConjOptimal := by
  native_decide

/-- **No plan of the instance is cheaper than the plan found.** -/
theorem transportLiteConjOptimal_optimal :
    ∀ σ', transportLiteConj.IsPlan σ' →
      transportLiteConj.planCost transportLiteConjOptimal ≤ transportLiteConj.planCost σ' :=
  solveOutcomeOptimal_optimal transportLiteConj_solveOptimal

/-- The plan found is also a plan, of course. -/
theorem transportLiteConjOptimal_isPlan : transportLiteConj.IsPlan transportLiteConjOptimal :=
  solveOutcomeOptimal_isPlan transportLiteConj_solveOptimal

/-! ### Unsolvability is still detected -/

theorem blocksImpossible_solveOutcomeFull :
    solveOutcomeFull blocksImpossible .blind 100 = .unsolvable := by
  native_decide

/-- The instance really has no plan. -/
theorem blocksImpossible_not_solvable_full : ¬ blocksImpossible.Solvable :=
  solveOutcomeFull_unsolvable blocksImpossible_solveOutcomeFull

end Examples
end PDDL
