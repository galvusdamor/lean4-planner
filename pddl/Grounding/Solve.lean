import pddl.Grounding.Positive
import pddl.Grounding.Reach
import planning.PlannerHeap

/-!
# The end to end PDDL solver: grounding plus the STRIPS planner of `planning`

This module closes the chain

```
PDDL source text --parse--> Instance --ground--> GroundTask --to STRIPS--> STRIPS.PlanningTask
                                                                                  |
                                                                        planner_heap_fast
                                                                                  |
                                                                                plan
```

No search is implemented here: the search is the A\* of the `planning` library
(`STRIPS.planner_heap_fast`, see `planning.PlannerHeap`), run on the `STRIPS.PlanningTask`
produced by the verified grounder.  What this module adds is

* `PDDL.GroundTask.opsOfPath`, which reads a path of the STRIPS task back as a list of
  ground operators of the ground task, together with its correctness proof
  `PDDL.GroundTask.opsOfPath_spec`;
* `PDDL.GroundTask.solveStrips`, the planner applied to `GroundTask.toSTRIPS`, proved sound
  (`solveStrips_isPlan`) and complete (`solveStrips_unsolvable`);
* `PDDL.solveOutcome`, the whole pipeline, with the two guarantees
  `PDDL.solveOutcome_isPlan` (a returned action sequence is a plan of the *lifted* PDDL
  instance, in the sense of `pddl.Semantics`) and `PDDL.solveOutcome_unsolvable` (an
  instance reported unsolvable really has no plan).

The pipeline is: reachability grounding (`PDDL.groundReachable`), compilation to positive
normal form (`PDDL.GroundTask.toPositive`), translation to `STRIPS.PlanningTask`
(`PDDL.GroundTask.toSTRIPS`), and finally the planner.  Instances whose ground task has
conditional effects or a non-conjunctive goal cannot be expressed as a `STRIPS.PlanningTask`
and yield the outcome `unknown`; nothing is claimed for them.

The heuristic passed to A\* is the blind heuristic `fun _ => 0`, so the search is a
uniform-cost search and the plans returned are cost optimal; the `planning` library's
heuristics can be plugged in instead (they must be admissible for
`STRIPS.planner_heap_fast_complete` to apply).
-/

namespace PDDL

namespace GroundTask

/-! ### Reading a STRIPS path back as a sequence of ground operators -/

/-- The ground operator a STRIPS action of `T.toSTRIPS` was translated from.  If several
operators translate to the same STRIPS action, the first one is returned; all of them have
the same precondition, effect and cost, so which one is picked does not matter. -/
def opOfAction (T : GroundTask) (a : STRIPS.Action T.numVars) : Option GroundOp :=
  T.ops.find? (fun op => op.action.toString == a.name && decide (T.toAction op = a))

theorem opOfAction_eq_some {T : GroundTask} {a : STRIPS.Action T.numVars} {op : GroundOp}
    (h : T.opOfAction a = some op) : op ∈ T.ops ∧ T.toAction op = a := by
  rw [opOfAction] at h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  exact ⟨List.mem_of_find?_eq_some h, hp.2⟩

theorem opOfAction_isSome {T : GroundTask} {a : STRIPS.Action T.numVars}
    (ha : a ∈ T.toSTRIPS.actions) : ∃ op, T.opOfAction a = some op := by
  obtain ⟨op, hop, rfl⟩ := exists_op_of_mem_actions ha
  have : (T.opOfAction (T.toAction op)).isSome := by
    rw [opOfAction, List.isSome_find?, List.any_eq_true]
    exact ⟨op, hop, by simp [toAction]⟩
  exact Option.isSome_iff_exists.1 this

/-- The sequence of ground operators along a path of the STRIPS task. -/
def opsOfPath (T : GroundTask) : {S S' : STRIPS.State T.numVars} →
    STRIPS.PlanningTask.Path T.toSTRIPS S S' → List GroundOp
  | _, _, .empty _ => []
  | _, _, .cons a _ _ _ p => (T.opOfAction a).toList ++ T.opsOfPath p

/-- **Correctness of the extraction**: the operator sequence read off a path of the STRIPS
task is an execution of the ground task between the corresponding states. -/
theorem opsOfPath_spec {T : GroundTask} (hready : T.StripsReady) :
    ∀ {S S' : STRIPS.State T.numVars} (p : STRIPS.PlanningTask.Path T.toSTRIPS S S')
      (s : State), S = T.encode s →
      ∃ s' : State, T.Execution s (T.opsOfPath p) s' ∧ S' = T.encode s' := by
  intro S S' p
  induction p with
  | empty S => intro s hs; exact ⟨s, Execution.nil s, hs⟩
  | @cons a S1 S2 S3 ha succ p ih =>
    intro s hs
    obtain ⟨op, hfind⟩ := opOfAction_isSome ha
    obtain ⟨hop, hEq⟩ := opOfAction_eq_some hfind
    obtain ⟨happ, hsucc⟩ := succ
    subst hs
    subst hEq
    have happ' : op.Applicable s :=
      (applicable_toAction_iff hop (hready.positive.1 op hop) s).1 happ
    have hS2 : S2 = T.encode (op.result s) := by
      rw [hsucc, encode_result (hready.unconditional op hop) s]
    obtain ⟨s', hexec, hs'⟩ := ih _ hS2
    refine ⟨s', ?_, hs'⟩
    have hops : T.opsOfPath (.cons (T.toAction op) S2 ha ⟨happ, hsucc⟩ p)
        = op :: T.opsOfPath p := by
      simp [opsOfPath, hfind]
    rw [hops]
    exact Execution.cons hop happ' hexec

/-- The sequence of ground operators of a plan of the STRIPS task. -/
def planOps (T : GroundTask) (p : STRIPS.PlanningTask.Plan T.toSTRIPS T.toSTRIPS.init) :
    List GroundOp :=
  T.opsOfPath p.path

/-- The operator sequence of a STRIPS plan is a plan of the ground task. -/
theorem planOps_isPlan {T : GroundTask} (hready : T.StripsReady)
    (p : STRIPS.PlanningTask.Plan T.toSTRIPS T.toSTRIPS.init) : T.IsPlan (T.planOps p) := by
  obtain ⟨s', hexec, hs'⟩ :=
    opsOfPath_spec hready p.path T.initState (by rw [toSTRIPS_init])
  refine ⟨s', hexec, (goalState_iff hready.conjGoal hready.positive.2 s').1 ?_⟩
  rw [← hs']
  exact p.goal

/-! ### Solving a ground task with the STRIPS planner of `planning` -/

/-- **Solving a STRIPS-ready ground task** with the A\* of the `planning` library, run on the
translation `GroundTask.toSTRIPS` with the heuristic `heur`. -/
def solveStripsWith (T : GroundTask) (heur : BitVec T.numVars → ℕ∞) : Option (List GroundOp) :=
  (STRIPS.planner_heap_fast T.toSTRIPS heur).map T.planOps

/-- **Solving a STRIPS-ready ground task** with the A\* of the `planning` library and the
blind heuristic, i.e. by a uniform-cost search. -/
def solveStrips (T : GroundTask) : Option (List GroundOp) := T.solveStripsWith (fun _ => 0)

/-- **Soundness**: the operator sequence returned by `solveStripsWith` is a plan of the
ground task, whatever heuristic was used. -/
theorem solveStripsWith_isPlan {T : GroundTask} (hready : T.StripsReady)
    {heur : BitVec T.numVars → ℕ∞} {π : List GroundOp}
    (h : T.solveStripsWith heur = some π) : T.IsPlan π := by
  unfold solveStripsWith at h
  cases hp : STRIPS.planner_heap_fast T.toSTRIPS heur with
  | none => rw [hp] at h; simp at h
  | some p =>
    rw [hp, Option.map_some, Option.some.injEq] at h
    subst h
    exact planOps_isPlan hready p

/-- **Completeness**: if `solveStripsWith` returns nothing and the heuristic is admissible,
the ground task is unsolvable. -/
theorem solveStripsWith_unsolvable {T : GroundTask} (hready : T.StripsReady)
    {heur : BitVec T.numVars → ℕ∞} (hadm : STRIPS.heur_admissible' T.toSTRIPS heur)
    (h : T.solveStripsWith heur = none) : ¬ T.Solvable := by
  have hnone : STRIPS.planner_heap_fast T.toSTRIPS heur = none := by
    unfold solveStripsWith at h
    cases hp : STRIPS.planner_heap_fast T.toSTRIPS heur with
    | none => rfl
    | some p => rw [hp] at h; simp at h
  have hempty := STRIPS.planner_heap_fast_complete T.toSTRIPS _ hadm hnone
  rw [← strips_solvable_iff hready]
  rintro ⟨p⟩
  exact hempty.false p

/-- **Soundness**: the operator sequence returned by `solveStrips` is a plan of the ground
task. -/
theorem solveStrips_isPlan {T : GroundTask} (hready : T.StripsReady) {π : List GroundOp}
    (h : T.solveStrips = some π) : T.IsPlan π :=
  solveStripsWith_isPlan hready h

/-- **Completeness**: if `solveStrips` returns nothing, the ground task is unsolvable. -/
theorem solveStrips_unsolvable {T : GroundTask} (hready : T.StripsReady)
    (h : T.solveStrips = none) : ¬ T.Solvable :=
  solveStripsWith_unsolvable hready (STRIPS.zero_heur_admissible' _) h

end GroundTask

/-! ### The end to end solver -/

/-- The outcome of the solver on a PDDL instance. -/
inductive SolveOutcome where
  /-- A plan was found. -/
  | plan (π : List GroundAction)
  /-- The instance is unsolvable. -/
  | unsolvable
  /-- Nothing could be determined (the grounder ran out of fuel, or the instance is outside
  the fragment that the grounder and the STRIPS translation support). -/
  | unknown
  deriving DecidableEq, Repr, Inhabited

/-- The ground task of an instance, in the form the STRIPS translation expects: grounded by
the reachability grounder and compiled to positive normal form.  `none` if the grounder ran
out of fuel or if the ground task cannot be expressed in STRIPS (conditional effects, a
non-conjunctive goal, or the reserved predicate name `¬` already in use). -/
def stripsTask (I : Instance) (groundFuel : Nat := 1000) : Option GroundTask :=
  match groundReachable I groundFuel with
  | none => none
  | some T =>
      if T.unconditionalB && T.conjunctiveGoalB && T.negFreshB then some T.toPositive
      else none

/-- **The PDDL solver**: ground the instance, translate the ground task to a
`STRIPS.PlanningTask` and run the A\* of the `planning` library on it. -/
def solveOutcome (I : Instance) (groundFuel : Nat := 1000) : SolveOutcome :=
  if I.domain.typesWellFormedB then
    match groundReachable I groundFuel with
    | none => .unknown
    | some T =>
      if T.unconditionalB && T.conjunctiveGoalB && T.negFreshB then
        match T.toPositive.solveStrips with
        | some π => .plan (π.map (·.action))
        | none => .unsolvable
      else .unknown
  else .unknown

/-- If the checks of `solveOutcome` succeed, the positive normal form of the ground task is
STRIPS ready. -/
theorem GroundTask.stripsReady_toPositive_of_checks {T : GroundTask}
    (h : (T.unconditionalB && T.conjunctiveGoalB && T.negFreshB) = true) :
    T.toPositive.StripsReady :=
  GroundTask.toPositive_stripsReady
    (GroundTask.conjunctiveGoalB_iff.1 (by simp_all))

/-- **Soundness of the solver**: whenever it returns an action sequence, that sequence is a
plan of the lifted PDDL instance. -/
theorem solveOutcome_isPlan {I : Instance} {groundFuel : Nat} {σ : List GroundAction}
    (h : solveOutcome I groundFuel = .plan σ) : I.IsPlan σ := by
  unfold solveOutcome at h
  split at h
  · rename_i hwf
    cases hT : groundReachable I groundFuel with
    | none => rw [hT] at h; simp at h
    | some T =>
      rw [hT] at h
      dsimp only at h
      by_cases hchk : (T.unconditionalB && T.conjunctiveGoalB && T.negFreshB) = true
      · rw [if_pos hchk] at h
        have huc : T.Unconditional := GroundTask.unconditionalB_iff.1 (by simp_all)
        have hfresh : T.NegFresh := GroundTask.negFreshB_iff.1 (by simp_all)
        cases hs : T.toPositive.solveStrips with
        | none => rw [hs] at h; simp at h
        | some π =>
          rw [hs] at h
          simp only [SolveOutcome.plan.injEq] at h
          subst h
          have hplan : T.toPositive.IsPlan π :=
            GroundTask.solveStrips_isPlan (GroundTask.stripsReady_toPositive_of_checks hchk) hs
          obtain ⟨π₀, rfl, hπ₀⟩ :=
            GroundTask.isPlan_of_toPositive_isPlan hfresh huc hplan
          refine (groundReachable_isPlan_iff hwf hT _).2 ⟨π₀, ?_, hπ₀⟩
          exact (GroundTask.map_action_map_encOp π₀).symm ▸ rfl
      · rw [if_neg hchk] at h; simp at h
  · simp at h

/-- **Completeness of the solver**: whenever it reports that the instance is unsolvable, the
lifted PDDL instance really has no plan. -/
theorem solveOutcome_unsolvable {I : Instance} {groundFuel : Nat}
    (h : solveOutcome I groundFuel = .unsolvable) : ¬ I.Solvable := by
  unfold solveOutcome at h
  split at h
  · rename_i hwf
    cases hT : groundReachable I groundFuel with
    | none => rw [hT] at h; simp at h
    | some T =>
      rw [hT] at h
      dsimp only at h
      by_cases hchk : (T.unconditionalB && T.conjunctiveGoalB && T.negFreshB) = true
      · rw [if_pos hchk] at h
        have huc : T.Unconditional := GroundTask.unconditionalB_iff.1 (by simp_all)
        have hfresh : T.NegFresh := GroundTask.negFreshB_iff.1 (by simp_all)
        cases hs : T.toPositive.solveStrips with
        | some π => rw [hs] at h; simp at h
        | none =>
          rw [groundReachable_solvable_iff hwf hT,
            ← GroundTask.toPositive_solvable_iff hfresh huc]
          exact GroundTask.solveStrips_unsolvable
            (GroundTask.stripsReady_toPositive_of_checks hchk) hs
      · rw [if_neg hchk] at h; simp at h
  · simp at h

/-- The solver, returning only the plan it found (if any). -/
def solveChecked (I : Instance) (groundFuel : Nat := 1000) : Option (List GroundAction) :=
  match solveOutcome I groundFuel with
  | .plan σ => some σ
  | _ => none

/-- **Unconditional soundness of the solver**: every action sequence returned by
`solveChecked` is a plan of the lifted PDDL instance. -/
theorem solveChecked_isPlan {I : Instance} {groundFuel : Nat} {σ : List GroundAction}
    (h : solveChecked I groundFuel = some σ) : I.IsPlan σ := by
  unfold solveChecked at h
  split at h
  · rename_i σ' hσ'
    rw [Option.some.injEq] at h
    subst h
    exact solveOutcome_isPlan hσ'
  · exact absurd h (by simp)

end PDDL
