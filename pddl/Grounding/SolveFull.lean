import pddl.Grounding.SolveHeur
import pddl.Grounding.GoalSplit

/-!
# The PDDL solver for the whole grounded fragment

`pddl.Grounding.Solve` and `pddl.Grounding.SolveHeur` ground a PDDL instance and hand the
result to the A\* of the `planning` library, but only if the ground task happens to have no
conditional effects and a conjunctive goal; otherwise they give up with the outcome
`unknown`.  With the two compilations of `pddl.Grounding.Unconditional` (expanding
conditional effects) and `pddl.Grounding.GoalSplit` (splitting a disjunctive goal into one
task per disjunct) that restriction disappears, and this module assembles the full pipeline

```
Instance --ground--> GroundTask --toUnconditional--> --toPositive--> one task per goal clause
                                                                              |
                                                                    A* of `planning`
                                                                              |
                                                                    cheapest plan found
```

`PDDL.solveOutcomeFull` returns `unknown` only if the type hierarchy of the domain is
malformed, if the grounder runs out of fuel, or if the reserved predicate name `¬` used by
the positive normal form already occurs in the instance — never because of a feature of the
supported fragment.

Its guarantees are the same as those of the restricted solver:
`PDDL.solveOutcomeFull_isPlan` (a returned action sequence is a plan of the *lifted* PDDL
semantics) and `PDDL.solveOutcomeFull_unsolvable` (an instance reported unsolvable really has
no plan).

Since the goal clauses are solved independently, the cheapest of the returned plans is
returned (`PDDL.GroundTask.bestPlan`, whose result is at most as expensive as any of the
candidates by `PDDL.GroundTask.bestPlan_le`).
-/

namespace PDDL

namespace GroundTask

/-! ### Choosing the cheapest of several plans -/

/-- The cheapest of a list of operator sequences (`none` for the empty list). -/
def bestPlan : List (List GroundOp) → Option (List GroundOp)
  | [] => none
  | π :: πs =>
      match bestPlan πs with
      | none => some π
      | some π' => if planCost π ≤ planCost π' then some π else some π'

theorem bestPlan_mem : ∀ {l : List (List GroundOp)} {π : List GroundOp},
    bestPlan l = some π → π ∈ l
  | [], π, h => by simp [bestPlan] at h
  | π₀ :: l, π, h => by
      simp only [bestPlan] at h
      cases hrec : bestPlan l with
      | none =>
        rw [hrec] at h
        simp only [Option.some.injEq] at h
        exact h ▸ List.mem_cons_self
      | some π' =>
        rw [hrec] at h
        dsimp only at h
        by_cases hle : planCost π₀ ≤ planCost π'
        · rw [if_pos hle, Option.some.injEq] at h
          exact h ▸ List.mem_cons_self
        · rw [if_neg hle, Option.some.injEq] at h
          exact h ▸ List.mem_cons_of_mem _ (bestPlan_mem hrec)

theorem bestPlan_eq_nil : ∀ {l : List (List GroundOp)}, bestPlan l = none → l = []
  | [], _ => rfl
  | π₀ :: l, h => by
      simp only [bestPlan] at h
      cases hrec : bestPlan l with
      | none => rw [hrec] at h; simp at h
      | some π' =>
        rw [hrec] at h
        dsimp only at h
        by_cases hle : planCost π₀ ≤ planCost π' <;> simp [hle] at h

/-- The plan chosen is at most as expensive as every candidate. -/
theorem bestPlan_le : ∀ {l : List (List GroundOp)} {π : List GroundOp},
    bestPlan l = some π → ∀ π' ∈ l, planCost π ≤ planCost π'
  | [], π, h => by simp [bestPlan] at h
  | π₀ :: l, π, h => by
      simp only [bestPlan] at h
      cases hrec : bestPlan l with
      | none =>
        rw [hrec] at h
        simp only [Option.some.injEq] at h
        subst h
        intro π' hπ'
        rcases List.mem_cons.1 hπ' with rfl | hmem
        · exact le_rfl
        · rw [bestPlan_eq_nil hrec] at hmem
          simp at hmem
      | some π₁ =>
        have hrest := bestPlan_le hrec
        rw [hrec] at h
        dsimp only at h
        by_cases hle : planCost π₀ ≤ planCost π₁
        · rw [if_pos hle, Option.some.injEq] at h
          subst h
          intro π' hπ'
          rcases List.mem_cons.1 hπ' with rfl | hmem
          · exact le_rfl
          · exact le_trans hle (hrest _ hmem)
        · rw [if_neg hle, Option.some.injEq] at h
          subst h
          intro π' hπ'
          rcases List.mem_cons.1 hπ' with rfl | hmem
          · exact le_of_not_ge hle
          · exact hrest _ hmem

/-! ### Solving a task with a disjunctive goal -/

/-- **Solving an unconditional, positive ground task with a possibly disjunctive goal**: run
the STRIPS planner once per goal clause and keep the cheapest plan. -/
def solveDisjHeur (T : GroundTask) (H : Heur) (te : ℕ := 0) : Option (List GroundOp) :=
  bestPlan (T.goal.filterMap (fun c => (T.goalClauseTask c).solveStripsHeur H te))

/-- **Soundness**: the operator sequence returned by `solveDisjHeur` is a plan of the
task. -/
theorem solveDisjHeur_isPlan {T : GroundTask} (huc : T.Unconditional) (hpos : T.Positive)
    {H : Heur} {te : ℕ} {π : List GroundOp} (h : T.solveDisjHeur H te = some π) :
    T.IsPlan π := by
  have hmem := bestPlan_mem h
  obtain ⟨c, hc, hsolve⟩ := List.mem_filterMap.1 hmem
  refine isPlan_iff_exists_clause.2 ⟨c, hc, ?_⟩
  exact solveStripsHeur_isPlan (goalClauseTask_stripsReady huc hpos hc) hsolve

/-- **Completeness**: if `solveDisjHeur` returns nothing, the task is unsolvable. -/
theorem solveDisjHeur_unsolvable {T : GroundTask} (huc : T.Unconditional) (hpos : T.Positive)
    {H : Heur} {te : ℕ} (h : T.solveDisjHeur H te = none) : ¬ T.Solvable := by
  have hnil := bestPlan_eq_nil h
  rintro hsolv
  obtain ⟨c, hc, hsolvc⟩ := solvable_iff_exists_clause.1 hsolv
  cases hs : (T.goalClauseTask c).solveStripsHeur H te with
  | none =>
    exact solveStripsHeur_unsolvable (goalClauseTask_stripsReady huc hpos hc) hs hsolvc
  | some π =>
    have : π ∈ T.goal.filterMap (fun c => (T.goalClauseTask c).solveStripsHeur H te) :=
      List.mem_filterMap.2 ⟨c, hc, hs⟩
    rw [hnil] at this
    simp at this

end GroundTask

/-! ### The end to end solver -/

/-- **The PDDL solver for the whole grounded fragment**: ground the instance, expand
conditional effects, compile to positive normal form, and solve one STRIPS task per goal
clause with the A\* of the `planning` library, keeping the cheapest plan. -/
def solveOutcomeFull (I : Instance) (H : Heur := .blind) (groundFuel : Nat := 1000)
    (te : ℕ := 0) : SolveOutcome :=
  if I.domain.typesWellFormedB then
    match groundReachable I groundFuel with
    | none => .unknown
    | some T =>
      if T.toUnconditional.negFreshB then
        match T.toUnconditional.toPositive.solveDisjHeur H te with
        | some π => .plan (π.map (·.action))
        | none => .unsolvable
      else .unknown
  else .unknown

/-- **Soundness of the full solver**: whenever it returns an action sequence, that sequence is
a plan of the lifted PDDL instance. -/
theorem solveOutcomeFull_isPlan {I : Instance} {H : Heur} {groundFuel : Nat} {te : ℕ}
    {σ : List GroundAction} (h : solveOutcomeFull I H groundFuel te = .plan σ) :
    I.IsPlan σ := by
  unfold solveOutcomeFull at h
  split at h
  · rename_i hwf
    cases hT : groundReachable I groundFuel with
    | none => rw [hT] at h; simp at h
    | some T =>
      rw [hT] at h
      dsimp only at h
      by_cases hchk : T.toUnconditional.negFreshB = true
      · rw [if_pos hchk] at h
        have hfresh : T.toUnconditional.NegFresh := GroundTask.negFreshB_iff.1 hchk
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
          obtain ⟨π₀, rfl, hπ₀⟩ :=
            GroundTask.isPlan_of_toPositive_isPlan hfresh huc hplan
          obtain ⟨π₁, hπ₁, hact, -⟩ := GroundTask.isPlan_of_toUnconditional_isPlan hπ₀
          refine (groundReachable_isPlan_iff hwf hT _).2 ⟨π₁, ?_, hπ₁⟩
          rw [hact, GroundTask.map_action_map_encOp]
      · rw [if_neg hchk] at h; simp at h
  · simp at h

/-- **Completeness of the full solver**: whenever it reports that the instance is unsolvable,
the lifted PDDL instance really has no plan. -/
theorem solveOutcomeFull_unsolvable {I : Instance} {H : Heur} {groundFuel : Nat} {te : ℕ}
    (h : solveOutcomeFull I H groundFuel te = .unsolvable) : ¬ I.Solvable := by
  unfold solveOutcomeFull at h
  split at h
  · rename_i hwf
    cases hT : groundReachable I groundFuel with
    | none => rw [hT] at h; simp at h
    | some T =>
      rw [hT] at h
      dsimp only at h
      by_cases hchk : T.toUnconditional.negFreshB = true
      · rw [if_pos hchk] at h
        have hfresh : T.toUnconditional.NegFresh := GroundTask.negFreshB_iff.1 hchk
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

/-- The full solver, returning only the plan it found (if any). -/
def solveFullChecked (I : Instance) (H : Heur := .blind) (groundFuel : Nat := 1000)
    (te : ℕ := 0) : Option (List GroundAction) :=
  match solveOutcomeFull I H groundFuel te with
  | .plan σ => some σ
  | _ => none

/-- **Unconditional soundness**: every action sequence returned by `solveFullChecked` is a plan
of the lifted PDDL instance. -/
theorem solveFullChecked_isPlan {I : Instance} {H : Heur} {groundFuel : Nat} {te : ℕ}
    {σ : List GroundAction} (h : solveFullChecked I H groundFuel te = some σ) : I.IsPlan σ := by
  unfold solveFullChecked at h
  split at h
  · rename_i σ' hσ'
    rw [Option.some.injEq] at h
    subst h
    exact solveOutcomeFull_isPlan hσ'
  · exact absurd h (by simp)

end PDDL
