import pddl.Grounding.Match
import pddl.Grounding.Correct

/-!
# Grounding by delete-relaxation reachability

Naive full grounding (`pddl.Grounding.Compile`) instantiates every action schema with every
type-correct tuple of objects, which is exponential in the number of parameters and
infeasible for many benchmarks.  The standard remedy, implemented here, is to instantiate
only the actions that can possibly become applicable:

* start from the atoms of the initial state;
* instantiate the schemas by *matching* the positive atoms of their preconditions against
  the atoms collected so far (`pddl.Grounding.Match`), which is a relational join rather
  than a full enumeration;
* add the atoms these operators can add, and iterate until nothing changes.

This computes a superset `R` of the atoms that are true in some reachable state (it is the
set of atoms reachable under the *delete relaxation*, where delete effects are ignored),
and the operators produced in the last round are the ones whose positive preconditions are
contained in `R`.  Every operator that is dropped has a positive precondition atom that can
never become true, so it can never be applied.

The correctness statements are the same as for full grounding:

* `groundReachable_isPlan_iff`: the plans of the resulting ground task are exactly the
  plans of the lifted instance (via `GroundOp.action`);
* `groundReachable_planCost`: with the same cost;
* `groundReachable_solvable_iff`: hence the same solvability.

The proof rests on two facts: the matching is complete (`reachInstantiations_complete`), so
no applicable action is missed, and the fixpoint condition checked by the algorithm implies
that every reachable state is contained in `R` (`Instance.execution_subset_reach`).
-/

namespace PDDL

/-! ### One round of the fixpoint computation -/

/-- Ground the instantiations of one schema obtained by matching against `R`. -/
def groundReachSchema (I : Instance) (R : List Atom) (a : Action) : Option (List GroundOp) :=
  if I.domain.findAction a.name = some a then
    groundInstances I a (reachInstantiations I R a)
  else
    some []

/-- Ground a list of schemas by matching against `R`. -/
def groundReachSchemas (I : Instance) (R : List Atom) : List Action → Option (List GroundOp)
  | [] => some []
  | a :: as => do
      let l ← groundReachSchema I R a
      let l' ← groundReachSchemas I R as
      pure (l ++ l')

/-- All operators whose positive preconditions are contained in `R`, and possibly a few
more (the matching may produce instantiations that do not satisfy the full precondition;
they are harmless). -/
def groundReachOps (I : Instance) (R : List Atom) : Option (List GroundOp) :=
  groundReachSchemas I R I.domain.actions

/-- One round of the reachability computation: add the atoms that the operators of the
current round can add. -/
def reachStep (I : Instance) (R : List Atom) : Option (List Atom) := do
  let ops ← groundReachOps I R
  pure (dedupAtoms (R ++ ops.flatMap GroundOp.addList))

/-- Every atom of `l` occurs in `l'`.  The atoms of `l'` are put into a hash set first,
which matters because the fixpoint below tests this on lists of thousands of atoms. -/
def containsAllB (l l' : List Atom) : Bool :=
  let s := Std.HashSet.ofList l'
  l.all (fun a => s.contains a)

theorem containsAllB_eq (l l' : List Atom) :
    containsAllB l l' = l.all (fun a => l'.contains a) := by
  simp [containsAllB, Std.HashSet.contains_ofList]

/-- Iterate `reachStep` until it adds nothing new; `none` if the fuel runs out. -/
def reachIter (I : Instance) : Nat → List Atom → Option (List Atom)
  | 0, _ => none
  | n + 1, R => do
      let R' ← reachStep I R
      if containsAllB R' R then some R else reachIter I n R'

/-- The atoms reachable under the delete relaxation, starting from the initial state. -/
def reachableAtoms (I : Instance) (fuel : Nat) : Option (List Atom) :=
  reachIter I fuel I.initAtoms

/-- **The reachability grounder**: grounds a PDDL instance, instantiating only the actions
that are reachable under the delete relaxation. -/
def groundReachable (I : Instance) (fuel : Nat := 1000) : Option GroundTask := do
  let R ← reachableAtoms I fuel
  let ops ← groundReachOps I R
  pure ⟨ops, I.initAtoms, groundFormula I Assign.id I.problem.goal⟩

/-! ### Soundness and completeness of the operator list -/

theorem groundReachSchema_sound {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    {R : List Atom} {a : Action} {l : List GroundOp} (h : groundReachSchema I R a = some l) :
    ∀ op ∈ l, OpSound I op := by
  simp only [groundReachSchema] at h
  split at h
  · rename_i hfind
    exact groundInstances_sound hwf hfind _ l
      (fun args hargs => reachInstantiations_wellTyped hwf hargs) h
  · simp only [Option.some.injEq] at h
    subst h
    simp

theorem groundReachSchema_complete {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    {R : List Atom} {a : Action} {l : List GroundOp}
    (hfind : I.domain.findAction a.name = some a) (h : groundReachSchema I R a = some l)
    (args : List Name) (s : State) (hs : ∀ x ∈ s, x ∈ R)
    (happ : I.Applicable ⟨a.name, args⟩ s) :
    ∃ op ∈ l, op.action = ⟨a.name, args⟩ ∧ op.Applicable s ∧ OpSound I op := by
  obtain ⟨a', hfind', hty, hpre⟩ := happ
  rw [hfind] at hfind'
  cases hfind'
  have hmatch : args ∈ reachInstantiations I R a := by
    refine reachInstantiations_complete hwf hty (fun pa hpa => ?_)
    exact hs _ (Formula.holds_posConjAtoms hpre pa hpa)
  simp only [groundReachSchema, if_pos hfind] at h
  exact groundInstances_complete hwf hfind _ l
    (fun args hargs => reachInstantiations_wellTyped hwf hargs) h args hmatch s
    ⟨a, hfind, hty, hpre⟩

theorem groundReachSchemas_sound {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    {R : List Atom} :
    ∀ (as : List Action) (l : List GroundOp), groundReachSchemas I R as = some l →
      ∀ op ∈ l, OpSound I op := by
  intro as
  induction as with
  | nil => intro l h; simp only [groundReachSchemas, Option.some.injEq] at h; subst h; simp
  | cons a as ih =>
    intro l h
    simp only [groundReachSchemas] at h
    cases h₁ : groundReachSchema I R a with
    | none => rw [h₁] at h; simp at h
    | some l₁ =>
      rw [h₁] at h
      cases h₂ : groundReachSchemas I R as with
      | none => rw [h₂] at h; simp at h
      | some l₂ =>
        rw [h₂] at h
        simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        intro op hop
        rcases List.mem_append.1 hop with hop | hop
        · exact groundReachSchema_sound hwf h₁ op hop
        · exact ih l₂ h₂ op hop

theorem groundReachSchemas_complete {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    {R : List Atom} :
    ∀ (as : List Action) (l : List GroundOp), groundReachSchemas I R as = some l →
      ∀ (a : Action), a ∈ as → I.domain.findAction a.name = some a →
      ∀ (args : List Name) (s : State), (∀ x ∈ s, x ∈ R) → I.Applicable ⟨a.name, args⟩ s →
        ∃ op ∈ l, op.action = ⟨a.name, args⟩ ∧ op.Applicable s ∧ OpSound I op := by
  intro as
  induction as with
  | nil => intro l _ a ha; cases ha
  | cons a as ih =>
    intro l h a' ha' hfind args s hs happ
    simp only [groundReachSchemas] at h
    cases h₁ : groundReachSchema I R a with
    | none => rw [h₁] at h; simp at h
    | some l₁ =>
      rw [h₁] at h
      cases h₂ : groundReachSchemas I R as with
      | none => rw [h₂] at h; simp at h
      | some l₂ =>
        rw [h₂] at h
        simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        rcases List.mem_cons.1 ha' with rfl | ha'
        · obtain ⟨op, hop, hact, happ', hsound⟩ :=
            groundReachSchema_complete hwf hfind h₁ args s hs happ
          exact ⟨op, List.mem_append.2 (Or.inl hop), hact, happ', hsound⟩
        · obtain ⟨op, hop, hact, happ', hsound⟩ := ih l₂ h₂ a' ha' hfind args s hs happ
          exact ⟨op, List.mem_append.2 (Or.inr hop), hact, happ', hsound⟩

/-- Every operator produced by the reachability grounder is sound. -/
theorem groundReachOps_sound {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    {R : List Atom} {l : List GroundOp} (h : groundReachOps I R = some l) :
    ∀ op ∈ l, OpSound I op :=
  groundReachSchemas_sound hwf _ l h

/-- Whenever a ground action is applicable in a state all of whose atoms belong to `R`, the
operators produced by matching against `R` contain an applicable operator for it. -/
theorem groundReachOps_complete {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    {R : List Atom} {l : List GroundOp} (h : groundReachOps I R = some l)
    (ga : GroundAction) (s : State) (hs : ∀ x ∈ s, x ∈ R) (happ : I.Applicable ga s) :
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
  exact groundReachSchemas_complete hwf _ l h a hmem hfind' ga.args s hs happ

/-! ### The fixpoint -/

/-- The operators generated for `R` add only atoms of `R`. -/
def AddsClosed (R : List Atom) (ops : List GroundOp) : Prop :=
  ∀ op ∈ ops, ∀ a ∈ op.addList, a ∈ R

theorem reachStep_mono {I : Instance} {R R' : List Atom} (h : reachStep I R = some R') :
    ∀ a ∈ R, a ∈ R' := by
  simp only [reachStep] at h
  cases hops : groundReachOps I R with
  | none => rw [hops] at h; simp at h
  | some ops =>
    rw [hops] at h
    simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
    subst h
    intro a ha
    simp [ha]

/-- The result of the fixpoint iteration contains the atoms it started from and is closed
under the operators it generates. -/
theorem reachIter_spec {I : Instance} :
    ∀ (n : Nat) (R Rf : List Atom), reachIter I n R = some Rf →
      (∀ a ∈ R, a ∈ Rf) ∧ ∃ ops, groundReachOps I Rf = some ops ∧ AddsClosed Rf ops := by
  intro n
  induction n with
  | zero => intro R Rf h; simp [reachIter] at h
  | succ n ih =>
    intro R Rf h
    simp only [reachIter] at h
    cases hstep : reachStep I R with
    | none => rw [hstep] at h; simp at h
    | some R' =>
      rw [hstep] at h
      simp only [Option.bind_eq_bind, Option.bind_some] at h
      by_cases hall : containsAllB R' R = true
      · rw [if_pos hall] at h
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨fun a ha => ha, ?_⟩
        simp only [reachStep] at hstep
        cases hops : groundReachOps I R with
        | none => rw [hops] at hstep; simp at hstep
        | some ops =>
          rw [hops] at hstep
          simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
            Option.some.injEq] at hstep
          refine ⟨ops, rfl, ?_⟩
          intro op hop a ha
          have hmem : a ∈ R' := by
            rw [← hstep]
            simp only [mem_dedupAtoms, List.mem_append, List.mem_flatMap]
            exact Or.inr ⟨op, hop, ha⟩
          have := List.all_eq_true.1 ((containsAllB_eq R' R) ▸ hall) a hmem
          simpa using this
      · rw [if_neg hall] at h
        obtain ⟨hsub, hclosed⟩ := ih R' Rf h
        exact ⟨fun a ha => hsub a (reachStep_mono hstep a ha), hclosed⟩

/-! ### Reachable states stay inside `R` -/

namespace Instance

/-- Every state reachable from a state inside `R` stays inside `R`, provided `R` is closed
under the operators generated for it. -/
theorem execution_subset_reach {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    {R : List Atom} {ops : List GroundOp} (hops : groundReachOps I R = some ops)
    (hclosed : AddsClosed R ops) {s s' : State} {π : List GroundAction}
    (hs : ∀ x ∈ s, x ∈ R) (h : I.Execution s π s') : ∀ x ∈ s', x ∈ R := by
  induction h with
  | nil s => exact hs
  | @cons s s' ga π happ hexec ih =>
    refine ih ?_
    obtain ⟨op, hop, hact, -, hsound⟩ := groundReachOps_complete hwf hops ga s hs happ
    intro x hx
    rw [← hact, ← hsound.result s] at hx
    rcases GroundOp.mem_result.1 hx with hadd | ⟨hmem, -⟩
    · exact hclosed op hop x (GroundOp.mem_addList_of_mem_addSet hadd)
    · exact hs x hmem

end Instance

/-! ### Correctness of the reachability grounder -/

theorem groundReachable_spec {I : Instance} {fuel : Nat} {T : GroundTask}
    (h : groundReachable I fuel = some T) :
    ∃ R, reachableAtoms I fuel = some R ∧ groundReachOps I R = some T.ops ∧
      T.init = I.initAtoms ∧ T.goal = groundFormula I Assign.id I.problem.goal := by
  simp only [groundReachable] at h
  cases hR : reachableAtoms I fuel with
  | none => rw [hR] at h; simp at h
  | some R =>
    rw [hR] at h
    simp only [Option.bind_eq_bind, Option.bind_some] at h
    cases hops : groundReachOps I R with
    | none => rw [hops] at h; simp at h
    | some ops =>
      rw [hops] at h
      simp only [Option.bind_some, Option.pure_def, Option.some.injEq] at h
      subst h
      exact ⟨R, rfl, hops, rfl, rfl⟩

/-- The atom set computed by the grounder contains the initial state and is closed under
the operators it generates. -/
theorem reachableAtoms_spec {I : Instance} {fuel : Nat} {R : List Atom}
    (h : reachableAtoms I fuel = some R) :
    (∀ a ∈ I.initAtoms, a ∈ R) ∧ ∃ ops, groundReachOps I R = some ops ∧ AddsClosed R ops :=
  reachIter_spec fuel I.initAtoms R h

theorem groundReachable_initState {I : Instance} {fuel : Nat} {T : GroundTask}
    (h : groundReachable I fuel = some T) : T.initState = I.initState := by
  obtain ⟨-, -, -, hinit, -⟩ := groundReachable_spec h
  ext a
  simp only [GroundTask.initState, Set.mem_setOf_eq, hinit, Instance.mem_initAtoms,
    Instance.initState]

theorem groundReachable_goalHolds {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    {fuel : Nat} {T : GroundTask} (h : groundReachable I fuel = some T) (s : State) :
    T.GoalHolds s ↔ I.GoalHolds s := by
  obtain ⟨-, -, -, -, hgoal⟩ := groundReachable_spec h
  rw [GroundTask.GoalHolds, hgoal]
  exact groundFormula_holds hwf s I.problem.goal Assign.id

/-- Every operator of the reachability grounding is sound. -/
theorem groundReachable_opSound {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    {fuel : Nat} {T : GroundTask} (h : groundReachable I fuel = some T) :
    ∀ op ∈ T.ops, OpSound I op := by
  obtain ⟨R, -, hops, -, -⟩ := groundReachable_spec h
  exact groundReachOps_sound hwf hops

/-- Every execution of the lifted instance starting inside `R` is an execution of the
reachability grounding: no applicable action of a reachable state was pruned. -/
theorem groundExecution_of_execution_reach {I : Instance}
    (hwf : I.domain.typesWellFormedB = true) {R : List Atom} {ops : List GroundOp}
    {T : GroundTask} (hTops : T.ops = ops) (hops : groundReachOps I R = some ops)
    (hclosed : AddsClosed R ops) :
    ∀ {s s' : State} {π : List GroundAction}, I.Execution s π s' → (∀ x ∈ s, x ∈ R) →
      ∃ ops' : List GroundOp, ops'.map (·.action) = π ∧ T.Execution s ops' s' := by
  intro s s' π hexec
  induction hexec with
  | nil s => intro _; exact ⟨[], rfl, GroundTask.Execution.nil s⟩
  | @cons s s' ga π happ hexec ih =>
    intro hs
    obtain ⟨op, hop, hact, happ', hsound⟩ := groundReachOps_complete hwf hops ga s hs happ
    have hres : op.result s = I.result ga s := hact ▸ hsound.result s
    have hnext : ∀ x ∈ I.result ga s, x ∈ R := by
      intro x hx
      rw [← hres] at hx
      rcases GroundOp.mem_result.1 hx with hadd | ⟨hmem, -⟩
      · exact hclosed op hop x (GroundOp.mem_addList_of_mem_addSet hadd)
      · exact hs x hmem
    obtain ⟨ops', hops', hexec'⟩ := ih hnext
    refine ⟨op :: ops', by simp [hact, hops'], GroundTask.Execution.cons (hTops ▸ hop) happ' ?_⟩
    rw [hres]
    exact hexec'

/-- **Soundness of the reachability grounding**: reading a plan of the ground task as a
sequence of ground actions yields a plan of the PDDL instance. -/
theorem isPlan_of_groundReachable_isPlan {I : Instance}
    (hwf : I.domain.typesWellFormedB = true) {fuel : Nat} {T : GroundTask}
    (h : groundReachable I fuel = some T) {π : List GroundOp} (hplan : T.IsPlan π) :
    I.IsPlan (π.map (·.action)) := by
  obtain ⟨s, hexec, hgoal⟩ := hplan
  refine ⟨s, ?_, (groundReachable_goalHolds hwf h s).1 hgoal⟩
  rw [← groundReachable_initState h]
  exact execution_of_groundExecution (groundReachable_opSound hwf h) hexec

/-- **Completeness of the reachability grounding**: every plan of the PDDL instance is the
sequence of ground actions of a plan of the ground task; in particular pruning the
unreachable operators loses no plan. -/
theorem groundReachable_isPlan_of_isPlan {I : Instance}
    (hwf : I.domain.typesWellFormedB = true) {fuel : Nat} {T : GroundTask}
    (h : groundReachable I fuel = some T) {σ : List GroundAction} (hplan : I.IsPlan σ) :
    ∃ π : List GroundOp, π.map (·.action) = σ ∧ T.IsPlan π := by
  obtain ⟨R, hR, hops, -, -⟩ := groundReachable_spec h
  obtain ⟨hinit, ops₀, hops₀, hclosed⟩ := reachableAtoms_spec hR
  have hopseq : ops₀ = T.ops := by rw [hops₀] at hops; exact (Option.some.inj hops)
  subst hopseq
  obtain ⟨s, hexec, hgoal⟩ := hplan
  have hs : ∀ x ∈ I.initState, x ∈ R := by
    intro x hx
    exact hinit x (Instance.mem_initAtoms.2 hx)
  obtain ⟨π, hπ, hexec'⟩ :=
    groundExecution_of_execution_reach hwf rfl hops₀ hclosed hexec hs
  refine ⟨π, hπ, s, ?_, (groundReachable_goalHolds hwf h s).2 hgoal⟩
  rw [groundReachable_initState h]
  exact hexec'

/-- **The reachability grounding preserves semantics**: the plans of the ground task are
exactly the plans of the PDDL instance. -/
theorem groundReachable_isPlan_iff {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    {fuel : Nat} {T : GroundTask} (h : groundReachable I fuel = some T)
    (σ : List GroundAction) :
    I.IsPlan σ ↔ ∃ π : List GroundOp, π.map (·.action) = σ ∧ T.IsPlan π := by
  constructor
  · exact groundReachable_isPlan_of_isPlan hwf h
  · rintro ⟨π, rfl, hplan⟩
    exact isPlan_of_groundReachable_isPlan hwf h hplan

/-- The reachability grounding preserves solvability. -/
theorem groundReachable_solvable_iff {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    {fuel : Nat} {T : GroundTask} (h : groundReachable I fuel = some T) :
    I.Solvable ↔ T.Solvable := by
  constructor
  · rintro ⟨σ, hplan⟩
    obtain ⟨π, -, hplan'⟩ := groundReachable_isPlan_of_isPlan hwf h hplan
    exact ⟨π, hplan'⟩
  · rintro ⟨π, hplan⟩
    exact ⟨_, isPlan_of_groundReachable_isPlan hwf h hplan⟩

/-- The reachability grounding preserves plan costs. -/
theorem groundReachable_planCost {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    {fuel : Nat} {T : GroundTask} (h : groundReachable I fuel = some T) {π : List GroundOp}
    (hplan : T.IsPlan π) : GroundTask.planCost π = I.planCost (π.map (·.action)) := by
  obtain ⟨s, hexec, -⟩ := hplan
  rw [Instance.planCost, ← groundReachable_initState h]
  exact planCost_eq_trajectoryCost (groundReachable_opSound hwf h) hexec

end PDDL
