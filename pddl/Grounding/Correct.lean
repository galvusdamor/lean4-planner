import pddl.Grounding.CompileCorrect

/-!
# Correctness of the grounder: operators and plans

Building on the formula and effect compiler correctness proofs of
`pddl.Grounding.CompileCorrect`, this module proves that the naive full grounding of
`pddl.Grounding.Compile` preserves the semantics of `pddl.Semantics`:

* `OpSound`: an operator produced by the grounder is applicable only when its ground
  action is, and then has the same successor state and the same cost;
* `groundOps_sound` / `groundOps_complete`: every operator of the grounding is sound, and
  whenever a ground action is applicable in a state, some operator of the grounding for
  that action is applicable in that state (there may be several operators per ground
  action, one per disjunct of its precondition);
* `groundInstance_isPlan_iff`, `groundInstance_solvable_iff` and
  `groundInstance_planCost`: plans of the ground task are exactly the plans of the
  instance (via `GroundOp.action`), with the same cost.
-/

namespace PDDL

/-! ### Grounding action schemas is correct -/

/-- A ground operator is *sound* for the instance `I` if it is applicable only when its
ground action is, and always has the same successor state and the same cost as its ground
action.  Completeness — that an applicable ground action has an applicable operator — is a
property of the operator *list*, see `groundOps_complete`. -/
structure OpSound (I : Instance) (op : GroundOp) : Prop where
  applicable : ∀ s : State, op.Applicable s → I.Applicable op.action s
  result : ∀ s : State, op.result s = I.result op.action s
  cost : ∀ s : State, op.cost = I.actionCost op.action s

/-- The shape of the operator list produced for one instantiation of an action schema. -/
theorem groundActionInstance_eq {I : Instance} {a : Action} {args : List Name}
    {l : List GroundOp} (h : groundActionInstance I a args = some l) :
    ∃ effs c, groundEffect I (bind a.params args) a.eff = some (effs, c) ∧
      l = (groundFormula I (bind a.params args) a.pre).map
        (fun pre => ⟨⟨a.name, args⟩, pre, effs, if I.usesActionCosts then c else 1⟩) := by
  simp only [groundActionInstance] at h
  cases heff : groundEffect I (bind a.params args) a.eff with
  | none => rw [heff] at h; simp at h
  | some p =>
    obtain ⟨effs, c⟩ := p
    rw [heff] at h
    simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
      Option.some.injEq] at h
    exact ⟨effs, c, rfl, h.symm⟩

/-- Grounding one instantiation of an action schema produces sound operators for the
corresponding ground action. -/
theorem groundActionInstance_sound {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    {a : Action} {args : List Name} {l : List GroundOp}
    (hfind : I.domain.findAction a.name = some a)
    (hargs : I.ArgsWellTyped a.params args)
    (h : groundActionInstance I a args = some l) :
    ∀ op ∈ l, op.action = ⟨a.name, args⟩ ∧ OpSound I op := by
  obtain ⟨effs, c, heff, rfl⟩ := groundActionInstance_eq h
  intro op hop
  obtain ⟨pre, hpre, rfl⟩ := List.mem_map.1 hop
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro s happ
    have hp : DnfHolds (groundFormula I (bind a.params args) a.pre) s ↔
        Formula.Holds I (bind a.params args) s a.pre :=
      groundFormula_holds hwf s a.pre _
    exact ⟨a, hfind, hargs, hp.1 ⟨pre, hpre, happ⟩⟩
  · intro s
    obtain ⟨hadd, hdel, -⟩ := groundEffect_spec hwf s a.eff _ _ _ heff
    simp only [GroundOp.result, Instance.result, hfind, Effect.apply, hadd, hdel,
      addSet_eq_addSetOf, delSet_eq_delSetOf]
  · intro s
    obtain ⟨-, -, hcost⟩ := groundEffect_spec hwf s a.eff _ _ _ heff
    simp only [Instance.actionCost, hfind, Instance.usesActionCosts, hcost]
    rfl

/-- Whenever the ground action of an instantiation is applicable in a state, one of the
operators produced for it is applicable in that state. -/
theorem groundActionInstance_complete {I : Instance}
    (hwf : I.domain.typesWellFormedB = true) {a : Action} {args : List Name}
    {l : List GroundOp} (hfind : I.domain.findAction a.name = some a)
    (h : groundActionInstance I a args = some l) (s : State)
    (happ : I.Applicable ⟨a.name, args⟩ s) : ∃ op ∈ l, op.Applicable s := by
  obtain ⟨effs, c, -, rfl⟩ := groundActionInstance_eq h
  obtain ⟨a', hfind', -, hholds⟩ := happ
  rw [hfind] at hfind'
  cases hfind'
  have hp : DnfHolds (groundFormula I (bind a.params args) a.pre) s :=
    (groundFormula_holds hwf s a.pre _).2 hholds
  obtain ⟨pre, hpre, hcl⟩ := hp
  exact ⟨_, List.mem_map_of_mem hpre, hcl⟩

/-! ### Soundness and completeness of the operator list -/

theorem groundInstances_sound {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    {a : Action} (hfind : I.domain.findAction a.name = some a) :
    ∀ (L : List (List Name)) (l : List GroundOp),
      (∀ args ∈ L, I.ArgsWellTyped a.params args) →
      groundInstances I a L = some l → ∀ op ∈ l, OpSound I op := by
  intro L
  induction L with
  | nil =>
    intro l _ h
    simp only [groundInstances, Option.some.injEq] at h
    subst h
    simp
  | cons args L ih =>
    intro l hty h op hop
    simp only [groundInstances] at h
    cases hr : groundActionInstance I a args with
    | none => rw [hr] at h; simp at h
    | some l₁ =>
      rw [hr] at h
      cases hrest : groundInstances I a L with
      | none => rw [hrest] at h; simp at h
      | some l' =>
        rw [hrest] at h
        simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        rcases List.mem_append.1 hop with hop | hop
        · exact (groundActionInstance_sound hwf hfind
            (hty args List.mem_cons_self) hr op hop).2
        · exact ih l' (fun x hx => hty x (List.mem_cons_of_mem _ hx)) hrest op hop

theorem groundInstances_complete {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    {a : Action} (hfind : I.domain.findAction a.name = some a) :
    ∀ (L : List (List Name)) (l : List GroundOp),
      (∀ args ∈ L, I.ArgsWellTyped a.params args) →
      groundInstances I a L = some l →
      ∀ args ∈ L, ∀ s : State, I.Applicable ⟨a.name, args⟩ s →
        ∃ op ∈ l, op.action = ⟨a.name, args⟩ ∧ op.Applicable s ∧ OpSound I op := by
  intro L
  induction L with
  | nil => intro l _ _ args hargs; cases hargs
  | cons args L ih =>
    intro l hty h args' hargs' s happ
    simp only [groundInstances] at h
    cases hr : groundActionInstance I a args with
    | none => rw [hr] at h; simp at h
    | some l₁ =>
      rw [hr] at h
      cases hrest : groundInstances I a L with
      | none => rw [hrest] at h; simp at h
      | some l' =>
        rw [hrest] at h
        simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        rcases List.mem_cons.1 hargs' with rfl | hargs'
        · obtain ⟨op, hop, happ'⟩ := groundActionInstance_complete hwf hfind hr s happ
          obtain ⟨hact, hsound⟩ := groundActionInstance_sound hwf hfind
            (hty _ List.mem_cons_self) hr op hop
          exact ⟨op, List.mem_append.2 (Or.inl hop), hact, happ', hsound⟩
        · obtain ⟨op, hop, hact, happ', hsound⟩ :=
            ih l' (fun x hx => hty x (List.mem_cons_of_mem _ hx)) hrest args' hargs' s happ
          exact ⟨op, List.mem_append.2 (Or.inr hop), hact, happ', hsound⟩

theorem groundActionSchema_sound {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    {a : Action} {l : List GroundOp} (h : groundActionSchema I a = some l) :
    ∀ op ∈ l, OpSound I op := by
  simp only [groundActionSchema] at h
  split at h
  · rename_i hfind
    exact groundInstances_sound hwf hfind _ l
      (fun args hargs => (Instance.mem_instantiations_iff hwf _ _).1 hargs) h
  · simp only [Option.some.injEq] at h
    subst h
    simp

theorem groundActionSchema_complete {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    {a : Action} {l : List GroundOp} (hfind : I.domain.findAction a.name = some a)
    (h : groundActionSchema I a = some l) (args : List Name) (s : State)
    (happ : I.Applicable ⟨a.name, args⟩ s) :
    ∃ op ∈ l, op.action = ⟨a.name, args⟩ ∧ op.Applicable s ∧ OpSound I op := by
  have hargs : I.ArgsWellTyped a.params args := by
    obtain ⟨a', hfind', hty, -⟩ := happ
    rw [hfind] at hfind'
    cases hfind'
    exact hty
  simp only [groundActionSchema, if_pos hfind] at h
  exact groundInstances_complete hwf hfind _ l
    (fun args hargs => (Instance.mem_instantiations_iff hwf _ _).1 hargs) h args
    ((Instance.mem_instantiations_iff hwf _ _).2 hargs) s happ

theorem groundSchemas_sound {I : Instance} (hwf : I.domain.typesWellFormedB = true) :
    ∀ (as : List Action) (l : List GroundOp), groundSchemas I as = some l →
      ∀ op ∈ l, OpSound I op := by
  intro as
  induction as with
  | nil => intro l h; simp only [groundSchemas, Option.some.injEq] at h; subst h; simp
  | cons a as ih =>
    intro l h
    simp only [groundSchemas] at h
    cases h₁ : groundActionSchema I a with
    | none => rw [h₁] at h; simp at h
    | some l₁ =>
      rw [h₁] at h
      cases h₂ : groundSchemas I as with
      | none => rw [h₂] at h; simp at h
      | some l₂ =>
        rw [h₂] at h
        simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
        subst h
        intro op hop
        rcases List.mem_append.1 hop with hop | hop
        · exact groundActionSchema_sound hwf h₁ op hop
        · exact ih l₂ h₂ op hop

theorem groundSchemas_complete {I : Instance} (hwf : I.domain.typesWellFormedB = true) :
    ∀ (as : List Action) (l : List GroundOp), groundSchemas I as = some l →
      ∀ (a : Action), a ∈ as → I.domain.findAction a.name = some a →
      ∀ (args : List Name) (s : State), I.Applicable ⟨a.name, args⟩ s →
        ∃ op ∈ l, op.action = ⟨a.name, args⟩ ∧ op.Applicable s ∧ OpSound I op := by
  intro as
  induction as with
  | nil => intro l _ a ha; cases ha
  | cons a as ih =>
    intro l h a' ha' hfind args s happ
    simp only [groundSchemas] at h
    cases h₁ : groundActionSchema I a with
    | none => rw [h₁] at h; simp at h
    | some l₁ =>
      rw [h₁] at h
      cases h₂ : groundSchemas I as with
      | none => rw [h₂] at h; simp at h
      | some l₂ =>
        rw [h₂] at h
        simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
        subst h
        rcases List.mem_cons.1 ha' with rfl | ha'
        · obtain ⟨op, hop, hact, happ', hsound⟩ :=
            groundActionSchema_complete hwf hfind h₁ args s happ
          exact ⟨op, List.mem_append.2 (Or.inl hop), hact, happ', hsound⟩
        · obtain ⟨op, hop, hact, happ', hsound⟩ := ih l₂ h₂ a' ha' hfind args s happ
          exact ⟨op, List.mem_append.2 (Or.inr hop), hact, happ', hsound⟩

/-- Every operator produced by the grounder is sound. -/
theorem groundOps_sound {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    {l : List GroundOp} (h : groundOps I = some l) : ∀ op ∈ l, OpSound I op :=
  groundSchemas_sound hwf _ l h

/-- Whenever a ground action is applicable in a state, the grounding contains an operator
for that action which is applicable in that state. -/
theorem groundOps_complete {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    {l : List GroundOp} (h : groundOps I = some l) (ga : GroundAction) (s : State)
    (happ : I.Applicable ga s) :
    ∃ op ∈ l, op.action = ga ∧ op.Applicable s ∧ OpSound I op := by
  obtain ⟨a, hfind, -, -⟩ := id happ
  have hmem : a ∈ I.domain.actions := List.mem_of_find?_eq_some hfind
  have hname : a.name = ga.name := by
    have := List.find?_some hfind
    simpa using this
  have hfind' : I.domain.findAction a.name = some a := by rw [hname]; exact hfind
  have hga : ga = ⟨a.name, ga.args⟩ := by
    cases ga; simp only [GroundAction.mk.injEq, and_true]; simpa using hname.symm
  rw [hga] at happ ⊢
  exact groundSchemas_complete hwf _ l h a hmem hfind' ga.args s happ

/-! ### Executions and plans -/

/-- Every execution of the ground task is an execution of the instance. -/
theorem execution_of_groundExecution {I : Instance} {T : GroundTask}
    (hsound : ∀ op ∈ T.ops, OpSound I op) {s s' : State} {π : List GroundOp}
    (h : T.Execution s π s') : I.Execution s (π.map (·.action)) s' := by
  induction h with
  | nil s => exact Instance.Execution.nil s
  | @cons s s' op π hop happ _ ih =>
    have hs := hsound op hop
    refine Instance.Execution.cons (hs.applicable s happ) ?_
    rw [← hs.result s]
    exact ih

/-- Every execution of the instance is an execution of the ground task. -/
theorem groundExecution_of_execution {I : Instance} {T : GroundTask}
    (hcomplete : ∀ (ga : GroundAction) (s : State), I.Applicable ga s →
      ∃ op ∈ T.ops, op.action = ga ∧ op.Applicable s ∧ OpSound I op)
    {s s' : State} {π : List GroundAction} (h : I.Execution s π s') :
    ∃ ops : List GroundOp, ops.map (·.action) = π ∧ T.Execution s ops s' := by
  induction h with
  | nil s => exact ⟨[], rfl, GroundTask.Execution.nil s⟩
  | @cons s s' ga π happ _ ih =>
    obtain ⟨op, hop, hact, happ', hs⟩ := hcomplete ga s happ
    have hres : op.result s = I.result ga s := hact ▸ hs.result s
    obtain ⟨ops, hops, hexec⟩ := ih
    refine ⟨op :: ops, by simp [hact, hops], GroundTask.Execution.cons hop happ' ?_⟩
    rw [hres]
    exact hexec

/-- The cost of an execution of the ground task equals the cost of the corresponding
trajectory of the instance. -/
theorem planCost_eq_trajectoryCost {I : Instance} {T : GroundTask}
    (hsound : ∀ op ∈ T.ops, OpSound I op) {s s' : State} {π : List GroundOp}
    (h : T.Execution s π s') :
    GroundTask.planCost π = I.trajectoryCost s (π.map (·.action)) := by
  induction h with
  | nil s => simp [GroundTask.planCost, Instance.trajectoryCost]
  | @cons s s' op π hop _ _ ih =>
    have hs := hsound op hop
    simp only [GroundTask.planCost, List.map_cons, List.sum_cons,
      Instance.trajectoryCost] at *
    rw [hs.cost s, ← hs.result s, ih]

/-! ### The grounding of an instance -/

theorem groundInstance_spec {I : Instance} {T : GroundTask} (h : groundInstance I = some T) :
    groundOps I = some T.ops ∧ T.init = I.initAtoms ∧
      T.goal = groundFormula I Assign.id I.problem.goal := by
  simp only [groundInstance] at h
  cases hops : groundOps I with
  | none => rw [hops] at h; simp at h
  | some ops =>
    rw [hops] at h
    simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
      Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl, rfl⟩

/-- The initial state of the ground task is the initial state of the instance. -/
theorem groundInstance_initState {I : Instance} {T : GroundTask}
    (h : groundInstance I = some T) : T.initState = I.initState := by
  obtain ⟨-, hinit, -⟩ := groundInstance_spec h
  ext a
  simp only [GroundTask.initState, Set.mem_setOf_eq, hinit, Instance.mem_initAtoms,
    Instance.initState]

/-- The goal of the ground task holds exactly when the goal of the instance does. -/
theorem groundInstance_goalHolds {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    {T : GroundTask} (h : groundInstance I = some T) (s : State) :
    T.GoalHolds s ↔ I.GoalHolds s := by
  obtain ⟨-, -, hgoal⟩ := groundInstance_spec h
  rw [GroundTask.GoalHolds, hgoal]
  exact groundFormula_holds hwf s I.problem.goal Assign.id

/-- Every operator of the grounding is sound. -/
theorem groundInstance_opSound {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    {T : GroundTask} (h : groundInstance I = some T) : ∀ op ∈ T.ops, OpSound I op :=
  groundOps_sound hwf (groundInstance_spec h).1

/-- Whenever a ground action is applicable, the grounding has an applicable operator for
it. -/
theorem groundInstance_opComplete {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    {T : GroundTask} (h : groundInstance I = some T) (ga : GroundAction) (s : State)
    (happ : I.Applicable ga s) :
    ∃ op ∈ T.ops, op.action = ga ∧ op.Applicable s ∧ OpSound I op :=
  groundOps_complete hwf (groundInstance_spec h).1 ga s happ

/-- **Soundness of the grounding**: reading a plan of the ground task as a sequence of
ground actions yields a plan of the PDDL instance. -/
theorem isPlan_of_groundIsPlan {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    {T : GroundTask} (h : groundInstance I = some T) {π : List GroundOp}
    (hplan : T.IsPlan π) : I.IsPlan (π.map (·.action)) := by
  obtain ⟨s, hexec, hgoal⟩ := hplan
  refine ⟨s, ?_, (groundInstance_goalHolds hwf h s).1 hgoal⟩
  rw [← groundInstance_initState h]
  exact execution_of_groundExecution (groundInstance_opSound hwf h) hexec

/-- **Completeness of the grounding**: every plan of the PDDL instance is the sequence of
ground actions of a plan of the ground task. -/
theorem groundIsPlan_of_isPlan {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    {T : GroundTask} (h : groundInstance I = some T) {σ : List GroundAction}
    (hplan : I.IsPlan σ) : ∃ π : List GroundOp, π.map (·.action) = σ ∧ T.IsPlan π := by
  obtain ⟨s, hexec, hgoal⟩ := hplan
  rw [← groundInstance_initState h] at hexec
  obtain ⟨π, hπ, hexec'⟩ :=
    groundExecution_of_execution (groundInstance_opComplete hwf h) hexec
  exact ⟨π, hπ, s, hexec', (groundInstance_goalHolds hwf h s).2 hgoal⟩

/-- **The grounding preserves semantics**: the plans of the ground task are exactly the
plans of the PDDL instance. -/
theorem groundInstance_isPlan_iff {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    {T : GroundTask} (h : groundInstance I = some T) (σ : List GroundAction) :
    I.IsPlan σ ↔ ∃ π : List GroundOp, π.map (·.action) = σ ∧ T.IsPlan π := by
  constructor
  · exact groundIsPlan_of_isPlan hwf h
  · rintro ⟨π, rfl, hplan⟩
    exact isPlan_of_groundIsPlan hwf h hplan

/-- The grounding preserves solvability. -/
theorem groundInstance_solvable_iff {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    {T : GroundTask} (h : groundInstance I = some T) : I.Solvable ↔ T.Solvable := by
  constructor
  · rintro ⟨σ, hplan⟩
    obtain ⟨π, -, hplan'⟩ := groundIsPlan_of_isPlan hwf h hplan
    exact ⟨π, hplan'⟩
  · rintro ⟨π, hplan⟩
    exact ⟨_, isPlan_of_groundIsPlan hwf h hplan⟩

/-- The grounding preserves plan costs. -/
theorem groundInstance_planCost {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    {T : GroundTask} (h : groundInstance I = some T) {π : List GroundOp}
    (hplan : T.IsPlan π) : GroundTask.planCost π = I.planCost (π.map (·.action)) := by
  obtain ⟨s, hexec, -⟩ := hplan
  rw [Instance.planCost, ← groundInstance_initState h]
  exact planCost_eq_trajectoryCost (groundInstance_opSound hwf h) hexec

end PDDL
