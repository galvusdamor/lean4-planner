import pddl.Grounding.SolveFull

/-!
# Cost optimality of the PDDL solver

The A\* of the `planning` library returns a cheapest plan when it is run with an admissible
heuristic (`STRIPS.planner_cached_fast_optimal`).  This module carries that guarantee along
the whole chain, so that it becomes a statement about the *lifted* PDDL instance: the plan
returned by `PDDL.solveOutcomeOptimal` is of minimal cost among all plans of the instance
(`PDDL.solveOutcomeOptimal_optimal`).

Two things have to be dealt with.

* `STRIPS.Action` has natural number costs and the translation of `pddl.Grounding.Strips`
  transports the integer cost of an operator with `Int.toNat`, so the correspondence between
  the cost of a path and the cost of the operator sequence it comes from only holds for
  tasks whose operators have nonnegative costs (`PDDL.GroundTask.NonnegCosts`).  This is
  checked by the solver (`PDDL.GroundTask.nonnegCostsB`), which is why
  `PDDL.solveOutcomeOptimal` is a separate function: unlike `PDDL.solveOutcomeFull` it
  answers `unknown` on an instance with a negative action cost, and claims nothing there.
* Every step of the pipeline preserves plan costs — the expansion of conditional effects
  (`toUnconditional_isPlan`), the positive normal form (`planCost_map_encOp`), the goal split
  (same operators) and the grounder (`groundReachable_planCost`) — and the cheapest of the
  plans found for the individual goal clauses is returned (`bestPlan_le`).
-/

namespace PDDL

namespace GroundTask

/-! ### Tasks with nonnegative costs -/

@[simp] theorem planCost_cons (op : GroundOp) (π : List GroundOp) :
    planCost (op :: π) = op.cost + planCost π := by
  simp [planCost]

/-- All operators of the task have a nonnegative cost. -/
def NonnegCosts (T : GroundTask) : Prop := ∀ op ∈ T.ops, 0 ≤ op.cost

/-- Executable check for `GroundTask.NonnegCosts`. -/
def nonnegCostsB (T : GroundTask) : Bool := T.ops.all (fun op => 0 ≤ op.cost)

theorem nonnegCostsB_iff {T : GroundTask} : T.nonnegCostsB = true ↔ T.NonnegCosts := by
  simp only [nonnegCostsB, List.all_eq_true, decide_eq_true_eq, NonnegCosts]

theorem toUnconditional_nonnegCosts {T : GroundTask} (h : T.NonnegCosts) :
    T.toUnconditional.NonnegCosts := by
  intro op' hop'
  obtain ⟨op, hop, hexp⟩ := mem_toUnconditional_ops hop'
  rw [GroundOp.cost_of_mem_expand hexp]
  exact h op hop

theorem toPositive_nonnegCosts {T : GroundTask} (h : T.NonnegCosts) :
    T.toPositive.NonnegCosts := by
  intro op' hop'
  obtain ⟨op, hop, rfl⟩ := List.mem_map.1 hop'
  exact h op hop

theorem goalClauseTask_nonnegCosts {T : GroundTask} (h : T.NonnegCosts) (c : List Lit) :
    (T.goalClauseTask c).NonnegCosts := h

/-! ### The cost of a path and the cost of an operator sequence -/

/-- The cost of the operator sequence read off a path is the cost of the path. -/
theorem planCost_opsOfPath {T : GroundTask} (hnn : T.NonnegCosts) :
    ∀ {S S' : STRIPS.State T.numVars} (p : STRIPS.PlanningTask.Path T.toSTRIPS S S'),
      planCost (T.opsOfPath p) = (p.cost : Int) := by
  intro S S' p
  induction p with
  | empty S => simp [opsOfPath, planCost, STRIPS.PlanningTask.Path.cost]
  | @cons a S1 S2 S3 ha succ p ih =>
    obtain ⟨op, hfind⟩ := opOfAction_isSome ha
    obtain ⟨hop, hEq⟩ := opOfAction_eq_some hfind
    have hcost : (a.cost : Int) = op.cost := by
      rw [← hEq]
      show ((op.cost.toNat : Int)) = op.cost
      exact Int.toNat_of_nonneg (hnn op hop)
    have hops : T.opsOfPath (.cons a S2 ha succ p) = op :: T.opsOfPath p := by
      simp [opsOfPath, hfind]
    rw [hops, planCost_cons, ih, STRIPS.PlanningTask.Path.cost]
    push_cast
    omega

/-- Every execution of the ground task gives a path of the same cost. -/
theorem exists_path_cost {T : GroundTask} (hready : T.StripsReady) (hnn : T.NonnegCosts)
    {s s' : State} {π : List GroundOp} (h : T.Execution s π s')
    {S : STRIPS.State T.numVars} (hS : S = T.encode s) :
    ∃ p : STRIPS.PlanningTask.Path T.toSTRIPS S (T.encode s'),
      (p.cost : Int) = planCost π := by
  subst hS
  induction h with
  | nil s => exact ⟨.empty _, by simp [STRIPS.PlanningTask.Path.cost, planCost]⟩
  | @cons s s' op π hop happ _ ih =>
    obtain ⟨p, hp⟩ := ih
    refine ⟨.cons (T.toAction op) (T.encode (op.result s)) (mem_toSTRIPS_actions hop)
      ⟨(applicable_toAction_iff hop (hready.positive.1 op hop) s).2 happ,
        encode_result (hready.unconditional op hop) s⟩ p, ?_⟩
    have hcost : ((T.toAction op).cost : Int) = op.cost := by
      show ((op.cost.toNat : Int)) = op.cost
      exact Int.toNat_of_nonneg (hnn op hop)
    rw [STRIPS.PlanningTask.Path.cost, planCost_cons, ← hp]
    push_cast
    omega

/-- Every plan of the ground task gives a plan of the STRIPS task of the same cost. -/
theorem exists_strips_plan_cost {T : GroundTask} (hready : T.StripsReady)
    (hnn : T.NonnegCosts) {π : List GroundOp} (h : T.IsPlan π) :
    ∃ q : STRIPS.PlanningTask.Plan T.toSTRIPS T.toSTRIPS.init,
      (q.path.cost : Int) = planCost π := by
  obtain ⟨s, hexec, hgoal⟩ := h
  obtain ⟨p, hp⟩ := exists_path_cost hready hnn hexec (toSTRIPS_init T)
  exact ⟨⟨T.encode s, p, (goalState_iff hready.conjGoal hready.positive.2 s).2 hgoal⟩, hp⟩

/-! ### Optimality of the STRIPS search -/

/-- **The plan returned for a STRIPS-ready task is a cheapest plan of that task.** -/
theorem solveStripsHeur_optimal {T : GroundTask} (hready : T.StripsReady)
    (hnn : T.NonnegCosts) {H : Heur} {te : ℕ} {π : List GroundOp}
    (h : T.solveStripsHeur H te = some π) :
    ∀ π', T.IsPlan π' → planCost π ≤ planCost π' := by
  intro π' hπ'
  unfold solveStripsHeur at h
  cases hp : STRIPS.planner_cached_fast T.toSTRIPS (H.toFun T.toSTRIPS) te with
  | none => rw [hp] at h; simp at h
  | some p =>
    rw [hp, Option.map_some, Option.some.injEq] at h
    subst h
    have hsome : (STRIPS.planner_cached_fast T.toSTRIPS (H.toFun T.toSTRIPS) te).isSome := by
      rw [hp]; rfl
    obtain ⟨q, hq⟩ := exists_strips_plan_cost hready hnn hπ'
    have hopt := STRIPS.planner_cached_fast_optimal T.toSTRIPS (H.toFun T.toSTRIPS) te
      (H.toFun_admissible T.toSTRIPS) hsome q
    have hget : (STRIPS.planner_cached_fast T.toSTRIPS (H.toFun T.toSTRIPS) te).get hsome = p := by
      simp [hp]
    rw [hget] at hopt
    have hleft : planCost (T.planOps p) = (p.path.cost : Int) := planCost_opsOfPath hnn p.path
    rw [hleft, ← hq]
    exact_mod_cast hopt

/-- **The plan returned for a task with a disjunctive goal is a cheapest plan.** -/
theorem solveDisjHeur_optimal {T : GroundTask} (huc : T.Unconditional) (hpos : T.Positive)
    (hnn : T.NonnegCosts) {H : Heur} {te : ℕ} {π : List GroundOp}
    (h : T.solveDisjHeur H te = some π) :
    ∀ π', T.IsPlan π' → planCost π ≤ planCost π' := by
  intro π' hπ'
  unfold solveDisjHeur at h
  obtain ⟨c, hc, hπc⟩ := isPlan_iff_exists_clause.1 hπ'
  cases hs : (T.goalClauseTask c).solveStripsHeur H te with
  | none =>
    exact absurd ⟨π', hπc⟩
      (solveStripsHeur_unsolvable (goalClauseTask_stripsReady huc hpos hc) hs)
  | some πc =>
    have hle1 : planCost πc ≤ planCost π' :=
      solveStripsHeur_optimal (goalClauseTask_stripsReady huc hpos hc)
        (goalClauseTask_nonnegCosts hnn c) hs π' hπc
    have hmem : πc ∈ T.goal.filterMap (fun c => (T.goalClauseTask c).solveStripsHeur H te) :=
      List.mem_filterMap.2 ⟨c, hc, hs⟩
    exact le_trans (bestPlan_le h _ hmem) hle1

end GroundTask

/-! ### The optimal end to end solver -/

/-- **The PDDL solver with a cost optimality guarantee**: as `PDDL.solveOutcomeFull`, but the
nonnegativity of the operator costs — needed to compare costs in the natural number costs of
`STRIPS.Action` — is checked as well. -/
def solveOutcomeOptimal (I : Instance) (H : Heur := .blind) (groundFuel : Nat := 1000)
    (te : ℕ := 0) : SolveOutcome :=
  if I.domain.typesWellFormedB then
    match groundReachable I groundFuel with
    | none => .unknown
    | some T =>
      if T.toUnconditional.negFreshB && T.nonnegCostsB then
        match T.toUnconditional.toPositive.solveDisjHeur H te with
        | some π => .plan (π.map (·.action))
        | none => .unsolvable
      else .unknown
  else .unknown

theorem solveOutcomeOptimal_isPlan {I : Instance} {H : Heur} {groundFuel : Nat} {te : ℕ}
    {σ : List GroundAction} (h : solveOutcomeOptimal I H groundFuel te = .plan σ) :
    I.IsPlan σ := by
  unfold solveOutcomeOptimal at h
  split at h
  · rename_i hwf
    cases hT : groundReachable I groundFuel with
    | none => rw [hT] at h; simp at h
    | some T =>
      rw [hT] at h
      dsimp only at h
      by_cases hchk : (T.toUnconditional.negFreshB && T.nonnegCostsB) = true
      · rw [if_pos hchk] at h
        have hfresh : T.toUnconditional.NegFresh :=
          GroundTask.negFreshB_iff.1 (by simp_all)
        have huc : T.toUnconditional.Unconditional := GroundTask.toUnconditional_unconditional T
        cases hs : T.toUnconditional.toPositive.solveDisjHeur H te with
        | none => rw [hs] at h; simp at h
        | some π =>
          rw [hs] at h
          simp only [SolveOutcome.plan.injEq] at h
          subst h
          have hplan : T.toUnconditional.toPositive.IsPlan π :=
            GroundTask.solveDisjHeur_isPlan (GroundTask.toPositive_unconditional _)
              (GroundTask.toPositive_positive _) hs
          obtain ⟨π₀, rfl, hπ₀⟩ := GroundTask.isPlan_of_toPositive_isPlan hfresh huc hplan
          obtain ⟨π₁, hπ₁, hact, -⟩ := GroundTask.isPlan_of_toUnconditional_isPlan hπ₀
          refine (groundReachable_isPlan_iff hwf hT _).2 ⟨π₁, ?_, hπ₁⟩
          rw [hact, GroundTask.map_action_map_encOp]
      · rw [if_neg hchk] at h; simp at h
  · simp at h

theorem solveOutcomeOptimal_unsolvable {I : Instance} {H : Heur} {groundFuel : Nat} {te : ℕ}
    (h : solveOutcomeOptimal I H groundFuel te = .unsolvable) : ¬ I.Solvable := by
  unfold solveOutcomeOptimal at h
  split at h
  · rename_i hwf
    cases hT : groundReachable I groundFuel with
    | none => rw [hT] at h; simp at h
    | some T =>
      rw [hT] at h
      dsimp only at h
      by_cases hchk : (T.toUnconditional.negFreshB && T.nonnegCostsB) = true
      · rw [if_pos hchk] at h
        have hfresh : T.toUnconditional.NegFresh :=
          GroundTask.negFreshB_iff.1 (by simp_all)
        have huc : T.toUnconditional.Unconditional := GroundTask.toUnconditional_unconditional T
        cases hs : T.toUnconditional.toPositive.solveDisjHeur H te with
        | some π => rw [hs] at h; simp at h
        | none =>
          rw [groundReachable_solvable_iff hwf hT,
            ← GroundTask.toUnconditional_solvable_iff T,
            ← GroundTask.toPositive_solvable_iff hfresh huc]
          exact GroundTask.solveDisjHeur_unsolvable (GroundTask.toPositive_unconditional _)
            (GroundTask.toPositive_positive _) hs
      · rw [if_neg hchk] at h; simp at h
  · simp at h

/-- **Cost optimality of the solver**: the plan it returns is of minimal cost among all plans
of the lifted PDDL instance. -/
theorem solveOutcomeOptimal_optimal {I : Instance} {H : Heur} {groundFuel : Nat} {te : ℕ}
    {σ : List GroundAction} (h : solveOutcomeOptimal I H groundFuel te = .plan σ) :
    ∀ σ', I.IsPlan σ' → I.planCost σ ≤ I.planCost σ' := by
  intro σ' hσ'
  unfold solveOutcomeOptimal at h
  split at h
  · rename_i hwf
    cases hT : groundReachable I groundFuel with
    | none => rw [hT] at h; simp at h
    | some T =>
      rw [hT] at h
      dsimp only at h
      by_cases hchk : (T.toUnconditional.negFreshB && T.nonnegCostsB) = true
      · rw [if_pos hchk] at h
        have hfresh : T.toUnconditional.NegFresh :=
          GroundTask.negFreshB_iff.1 (by simp_all)
        have hnn : T.NonnegCosts := GroundTask.nonnegCostsB_iff.1 (by simp_all)
        have huc : T.toUnconditional.Unconditional := GroundTask.toUnconditional_unconditional T
        have hnnP : T.toUnconditional.toPositive.NonnegCosts :=
          GroundTask.toPositive_nonnegCosts (GroundTask.toUnconditional_nonnegCosts hnn)
        cases hs : T.toUnconditional.toPositive.solveDisjHeur H te with
        | none => rw [hs] at h; simp at h
        | some π =>
          rw [hs] at h
          simp only [SolveOutcome.plan.injEq] at h
          subst h
          have hplan : T.toUnconditional.toPositive.IsPlan π :=
            GroundTask.solveDisjHeur_isPlan (GroundTask.toPositive_unconditional _)
              (GroundTask.toPositive_positive _) hs
          obtain ⟨π₀, rfl, hπ₀⟩ := GroundTask.isPlan_of_toPositive_isPlan hfresh huc hplan
          obtain ⟨π₁, hπ₁, hact, hcost₁⟩ := GroundTask.isPlan_of_toUnconditional_isPlan hπ₀
          -- the cost of the plan returned
          have hσ : (π₀.map GroundTask.encOp).map (·.action) = π₁.map (·.action) := by
            rw [GroundTask.map_action_map_encOp, hact]
          have hleft : I.planCost ((π₀.map GroundTask.encOp).map (·.action))
              = GroundTask.planCost (π₀.map GroundTask.encOp) := by
            rw [hσ, ← groundReachable_planCost hwf hT hπ₁, hcost₁,
              GroundTask.planCost_map_encOp]
          -- the cost of an arbitrary plan of the instance
          obtain ⟨π', hmap', hπ'⟩ := (groundReachable_isPlan_iff hwf hT σ').1 hσ'
          have hcost' : GroundTask.planCost π' = I.planCost σ' := by
            rw [← hmap']
            exact groundReachable_planCost hwf hT hπ'
          obtain ⟨π'', hπ'', -, hcost''⟩ := GroundTask.toUnconditional_isPlan hπ'
          have hπP : T.toUnconditional.toPositive.IsPlan (π''.map GroundTask.encOp) :=
            GroundTask.toPositive_isPlan hfresh huc hπ''
          have hopt := GroundTask.solveDisjHeur_optimal (GroundTask.toPositive_unconditional _)
            (GroundTask.toPositive_positive _) hnnP hs _ hπP
          rw [hleft, ← hcost', ← hcost'']
          exact le_of_le_of_eq hopt (GroundTask.planCost_map_encOp π'')
      · rw [if_neg hchk] at h; simp at h
  · simp at h

end PDDL
