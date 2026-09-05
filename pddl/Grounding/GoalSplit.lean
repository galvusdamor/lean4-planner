import pddl.Grounding.Unconditional

/-!
# Splitting a disjunctive goal

The goal of a ground task is a disjunction of conjunctions of literals
(`PDDL.GroundTask.goal : Dnf`), because a PDDL goal may be disjunctive.  The STRIPS
interface of the `planning` library only has conjunctive goals, so a task with a proper
disjunction could not be handed to the planner.

Rather than encoding the disjunction with additional atoms and operators — which changes
the operator set and the plan length — this module splits the task: for each goal clause
`c` there is the task `PDDL.GroundTask.goalClauseTask T c`, which has the same operators,
the same initial state and the single goal clause `c`.  A plan of the original task is
exactly a plan of one of these tasks (`PDDL.GroundTask.isPlan_iff_exists_clause`), so
solving them one by one and keeping the cheapest plan solves the original task; this is what
`pddl.Grounding.SolveFull` does.

The number of tasks is the number of goal disjuncts, which is one for the usual conjunctive
goal, so nothing changes for the common case.
-/

namespace PDDL

namespace GroundTask

/-- Executions only depend on the operators of a task. -/
theorem execution_congr {T T' : GroundTask} (hops : T.ops = T'.ops) {s s' : State}
    {π : List GroundOp} (h : T.Execution s π s') : T'.Execution s π s' := by
  induction h with
  | nil s => exact Execution.nil s
  | cons hop happ _ ih => exact Execution.cons (hops ▸ hop) happ ih

/-- The task with the same operators and initial state, but only the goal clause `c`. -/
def goalClauseTask (T : GroundTask) (c : List Lit) : GroundTask where
  ops := T.ops
  init := T.init
  goal := [c]

@[simp] theorem goalClauseTask_ops (T : GroundTask) (c : List Lit) :
    (T.goalClauseTask c).ops = T.ops := rfl

@[simp] theorem goalClauseTask_init (T : GroundTask) (c : List Lit) :
    (T.goalClauseTask c).init = T.init := rfl

@[simp] theorem goalClauseTask_initState (T : GroundTask) (c : List Lit) :
    (T.goalClauseTask c).initState = T.initState := rfl

@[simp] theorem goalClauseTask_goalHolds {T : GroundTask} {c : List Lit} {s : State} :
    (T.goalClauseTask c).GoalHolds s ↔ ClauseHolds c s := by
  simp [GoalHolds, goalClauseTask, DnfHolds]

theorem goalClauseTask_conjunctiveGoal (T : GroundTask) (c : List Lit) :
    (T.goalClauseTask c).ConjunctiveGoal := ⟨c, rfl⟩

theorem goalClauseTask_unconditional {T : GroundTask} (h : T.Unconditional) (c : List Lit) :
    (T.goalClauseTask c).Unconditional := h

theorem goalClauseTask_positive {T : GroundTask} (h : T.Positive) {c : List Lit}
    (hc : c ∈ T.goal) : (T.goalClauseTask c).Positive := by
  refine ⟨h.1, ?_⟩
  intro c' hc' l hl
  simp only [goalClauseTask, List.mem_singleton] at hc'
  exact h.2 c hc l (hc' ▸ hl)

/-- A task with a single goal clause coming from a positive, unconditional task can be
translated to STRIPS. -/
theorem goalClauseTask_stripsReady {T : GroundTask} (huc : T.Unconditional)
    (hpos : T.Positive) {c : List Lit} (hc : c ∈ T.goal) :
    (T.goalClauseTask c).StripsReady :=
  ⟨goalClauseTask_unconditional huc c, goalClauseTask_positive hpos hc,
    goalClauseTask_conjunctiveGoal T c⟩

/-- **A plan of the task is a plan for one of its goal clauses, and conversely.** -/
theorem isPlan_iff_exists_clause {T : GroundTask} {π : List GroundOp} :
    T.IsPlan π ↔ ∃ c ∈ T.goal, (T.goalClauseTask c).IsPlan π := by
  constructor
  · rintro ⟨s, hexec, c, hc, hcl⟩
    exact ⟨c, hc, s, execution_congr (T := T) (T' := T.goalClauseTask c) rfl hexec, by simpa using hcl⟩
  · rintro ⟨c, hc, s, hexec, hgoal⟩
    exact ⟨s, execution_congr (T := T.goalClauseTask c) (T' := T) rfl hexec, c, hc, by simpa using hgoal⟩

/-- **The task is solvable iff one of its goal clauses is achievable.** -/
theorem solvable_iff_exists_clause {T : GroundTask} :
    T.Solvable ↔ ∃ c ∈ T.goal, (T.goalClauseTask c).Solvable := by
  constructor
  · rintro ⟨π, hπ⟩
    obtain ⟨c, hc, hπ'⟩ := isPlan_iff_exists_clause.1 hπ
    exact ⟨c, hc, π, hπ'⟩
  · rintro ⟨c, hc, π, hπ⟩
    exact ⟨π, isPlan_iff_exists_clause.2 ⟨c, hc, hπ⟩⟩

end GroundTask

end PDDL
