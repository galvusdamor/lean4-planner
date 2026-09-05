import pddl.TypeHierarchy

/-!
# Executable evaluation of the PDDL semantics

`pddl.Semantics` defines the meaning of formulas, effects and plans as `Prop`s over
`Set Atom`.  This module gives *executable* counterparts (`Formula.evalB`, `Effect.addL`,
`Effect.applyB`, `Instance.validPlanB`, …) and proves that they agree with the
declarative semantics.  All statements assume `Domain.typesWellFormedB`, the (checkable)
condition under which the executable subtype test decides the subtype relation; see
`pddl.TypeHierarchy`.

The main results are

* `Formula.evalB_iff`: the Boolean evaluator decides satisfaction of goal descriptions,
* `Effect.mem_addL_iff` / `Effect.mem_delL_iff` / `Effect.toState_applyB`: the executable
  effect application computes the semantic successor state,
* `Instance.validPlanB_iff`: the executable plan validator decides `Instance.IsPlan`.

Together these give a verified plan validator for the lifted semantics.
-/

namespace PDDL

/-- The state described by a Boolean state representation. -/
def toState (s : Atom → Bool) : State := {a : Atom | s a = true}

@[simp] theorem mem_toState {s : Atom → Bool} {a : Atom} : a ∈ toState s ↔ s a = true := Iff.rfl

/-! ### Evaluating goal descriptions -/

namespace Formula

/-- Boolean evaluation of a goal description. -/
def evalB (I : Instance) (σ : Assign) (s : Atom → Bool) : Formula → Bool
  | .top => true
  | .bot => false
  | .atom p args => s (groundAtom σ p args)
  | .eq t₁ t₂ => t₁.inst σ == t₂.inst σ
  | .neg f => !evalB I σ s f
  | .conj f g => evalB I σ s f && evalB I σ s g
  | .disj f g => evalB I σ s f || evalB I σ s g
  | .imp f g => !evalB I σ s f || evalB I σ s g
  | .all v ty f => (I.objectsOfTypeL ty).all (fun o => evalB I (σ.set v o) s f)
  | .ex v ty f => (I.objectsOfTypeL ty).any (fun o => evalB I (σ.set v o) s f)

/-- The Boolean evaluator decides satisfaction of goal descriptions. -/
theorem evalB_iff {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    (s : Atom → Bool) (f : Formula) (σ : Assign) :
    evalB I σ s f = true ↔ Holds I σ (toState s) f := by
  induction f generalizing σ with
  | top => simp [evalB]
  | bot => simp [evalB]
  | atom p args => simp [evalB, Holds]
  | eq t₁ t₂ => simp [evalB, Holds]
  | neg f ih =>
    simp only [evalB, Holds, ← ih]
    cases h : evalB I σ s f <;> simp
  | conj f g ihf ihg => simp [evalB, Holds, ihf, ihg]
  | disj f g ihf ihg => simp [evalB, Holds, ihf, ihg]
  | imp f g ihf ihg =>
    simp only [evalB, Holds, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      ← ihf, ← ihg]
    cases h : evalB I σ s f <;> simp
  | all v ty f ih =>
    simp only [evalB, List.all_eq_true, Holds, ih]
    constructor
    · exact fun h o ho => h o ((Instance.mem_objectsOfTypeL_iff hwf o ty).2 ho)
    · exact fun h o ho => h o ((Instance.mem_objectsOfTypeL_iff hwf o ty).1 ho)
  | ex v ty f ih =>
    simp only [evalB, List.any_eq_true, Holds, ih]
    constructor
    · rintro ⟨o, ho, h⟩
      exact ⟨o, (Instance.mem_objectsOfTypeL_iff hwf o ty).1 ho, h⟩
    · rintro ⟨o, ho, h⟩
      exact ⟨o, (Instance.mem_objectsOfTypeL_iff hwf o ty).2 ho, h⟩

end Formula

/-! ### Applying effects -/

namespace Effect

/-- The list of atoms added by an effect. -/
def addL (I : Instance) (σ : Assign) (s : Atom → Bool) : Effect → List Atom
  | .nil => []
  | .add p args => [groundAtom σ p args]
  | .del _ _ => []
  | .conj e₁ e₂ => addL I σ s e₁ ++ addL I σ s e₂
  | .all v ty e => (I.objectsOfTypeL ty).flatMap (fun o => addL I (σ.set v o) s e)
  | .when c e => if Formula.evalB I σ s c then addL I σ s e else []
  | .incCost _ => []

/-- The list of atoms deleted by an effect. -/
def delL (I : Instance) (σ : Assign) (s : Atom → Bool) : Effect → List Atom
  | .nil => []
  | .add _ _ => []
  | .del p args => [groundAtom σ p args]
  | .conj e₁ e₂ => delL I σ s e₁ ++ delL I σ s e₂
  | .all v ty e => (I.objectsOfTypeL ty).flatMap (fun o => delL I (σ.set v o) s e)
  | .when c e => if Formula.evalB I σ s c then delL I σ s e else []
  | .incCost _ => []

theorem mem_addL_iff {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    (s : Atom → Bool) (e : Effect) (σ : Assign) (a : Atom) :
    a ∈ addL I σ s e ↔ a ∈ addSet I σ (toState s) e := by
  induction e generalizing σ with
  | nil => simp [addL, addSet]
  | add p args => simp [addL, addSet]
  | del p args => simp [addL, addSet]
  | conj e₁ e₂ ih₁ ih₂ => simp [addL, addSet, ih₁, ih₂]
  | all v ty e ih =>
    simp only [addL, addSet, List.mem_flatMap, Set.mem_setOf_eq, ih]
    constructor
    · rintro ⟨o, ho, h⟩
      exact ⟨o, (Instance.mem_objectsOfTypeL_iff hwf o ty).1 ho, h⟩
    · rintro ⟨o, ho, h⟩
      exact ⟨o, (Instance.mem_objectsOfTypeL_iff hwf o ty).2 ho, h⟩
  | when c e ih =>
    by_cases hc : Formula.evalB I σ s c = true
    · have hc' : Formula.Holds I σ (toState s) c := (Formula.evalB_iff hwf s c σ).1 hc
      simp [addL, addSet, hc, hc', ih]
    · have hc' : ¬ Formula.Holds I σ (toState s) c := fun h =>
        hc ((Formula.evalB_iff hwf s c σ).2 h)
      simp [addL, addSet, hc, hc']
  | incCost e => simp [addL, addSet]

theorem mem_delL_iff {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    (s : Atom → Bool) (e : Effect) (σ : Assign) (a : Atom) :
    a ∈ delL I σ s e ↔ a ∈ delSet I σ (toState s) e := by
  induction e generalizing σ with
  | nil => simp [delL, delSet]
  | add p args => simp [delL, delSet]
  | del p args => simp [delL, delSet]
  | conj e₁ e₂ ih₁ ih₂ => simp [delL, delSet, ih₁, ih₂]
  | all v ty e ih =>
    simp only [delL, delSet, List.mem_flatMap, Set.mem_setOf_eq, ih]
    constructor
    · rintro ⟨o, ho, h⟩
      exact ⟨o, (Instance.mem_objectsOfTypeL_iff hwf o ty).1 ho, h⟩
    · rintro ⟨o, ho, h⟩
      exact ⟨o, (Instance.mem_objectsOfTypeL_iff hwf o ty).2 ho, h⟩
  | when c e ih =>
    by_cases hc : Formula.evalB I σ s c = true
    · have hc' : Formula.Holds I σ (toState s) c := (Formula.evalB_iff hwf s c σ).1 hc
      simp [delL, delSet, hc, hc', ih]
    · have hc' : ¬ Formula.Holds I σ (toState s) c := fun h =>
        hc ((Formula.evalB_iff hwf s c σ).2 h)
      simp [delL, delSet, hc, hc']
  | incCost e => simp [delL, delSet]

/-- Executable application of an effect to a Boolean state. -/
def applyB (I : Instance) (σ : Assign) (s : Atom → Bool) (e : Effect) : Atom → Bool :=
  fun a => (addL I σ s e).contains a || (s a && !(delL I σ s e).contains a)

/-- The executable effect application computes the semantic successor state. -/
theorem toState_applyB {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    (s : Atom → Bool) (σ : Assign) (e : Effect) :
    toState (applyB I σ s e) = apply I σ (toState s) e := by
  ext a
  simp only [mem_toState, applyB, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true, List.contains_eq_mem, decide_eq_true_eq, decide_eq_false_iff_not,
    mem_apply, mem_addL_iff hwf, mem_delL_iff hwf]

end Effect

/-! ### Executable plan validation -/

namespace Instance

/-- Executable version of `Instance.initState`. -/
def initStateB (I : Instance) : Atom → Bool :=
  fun a => decide (InitEl.atom a.pred a.args ∈ I.problem.init)

@[simp] theorem toState_initStateB (I : Instance) : toState I.initStateB = I.initState := by
  ext a; simp [toState, initStateB, Instance.initState]

/-- Executable version of `Instance.ArgsWellTyped`. -/
def argsWellTypedB (I : Instance) : List TypedVar → List Name → Bool
  | [], [] => true
  | p :: ps, o :: os => I.hasTypeB o p.type && I.argsWellTypedB ps os
  | _, _ => false

theorem argsWellTypedB_iff {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    (params : List TypedVar) (args : List Name) :
    I.argsWellTypedB params args = true ↔ I.ArgsWellTyped params args := by
  induction params generalizing args with
  | nil =>
    cases args with
    | nil => simp [argsWellTypedB, ArgsWellTyped]
    | cons o os =>
      simp only [argsWellTypedB, ArgsWellTyped, Bool.false_eq_true, false_iff]
      intro h; cases h
  | cons p ps ih =>
    cases args with
    | nil =>
      simp only [argsWellTypedB, ArgsWellTyped, Bool.false_eq_true, false_iff]
      intro h; cases h
    | cons o os =>
      simp only [argsWellTypedB, ArgsWellTyped, Bool.and_eq_true, ih,
        hasTypeB_iff hwf]
      constructor
      · rintro ⟨h₁, h₂⟩; exact List.Forall₂.cons h₁ h₂
      · rintro (_ | ⟨h₁, h₂⟩); exact ⟨h₁, h₂⟩

/-- Executable version of `Instance.Applicable`. -/
def applicableB (I : Instance) (ga : GroundAction) (s : Atom → Bool) : Bool :=
  match I.domain.findAction ga.name with
  | some a =>
      I.argsWellTypedB a.params ga.args &&
        Formula.evalB I (bind a.params ga.args) s a.pre
  | none => false

theorem applicableB_iff {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    (ga : GroundAction) (s : Atom → Bool) :
    I.applicableB ga s = true ↔ I.Applicable ga (toState s) := by
  unfold applicableB Applicable
  cases ha : I.domain.findAction ga.name with
  | none => simp
  | some a =>
    simp only [Bool.and_eq_true, argsWellTypedB_iff hwf, Formula.evalB_iff hwf]
    constructor
    · rintro ⟨h₁, h₂⟩; exact ⟨a, rfl, h₁, h₂⟩
    · rintro ⟨a', ha', h₁, h₂⟩
      cases ha'
      exact ⟨h₁, h₂⟩

/-- Executable version of `Instance.result`. -/
def resultB (I : Instance) (ga : GroundAction) (s : Atom → Bool) : Atom → Bool :=
  match I.domain.findAction ga.name with
  | some a => Effect.applyB I (bind a.params ga.args) s a.eff
  | none => s

theorem toState_resultB {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    (ga : GroundAction) (s : Atom → Bool) :
    toState (I.resultB ga s) = I.result ga (toState s) := by
  unfold resultB result
  cases I.domain.findAction ga.name with
  | none => rfl
  | some a => exact Effect.toState_applyB hwf s _ a.eff

/-- Execute a sequence of ground actions, returning the resulting state if every action was
applicable. -/
def executeB (I : Instance) (s : Atom → Bool) : List GroundAction → Option (Atom → Bool)
  | [] => some s
  | ga :: π => if I.applicableB ga s then I.executeB (I.resultB ga s) π else none

theorem executeB_sound {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    (π : List GroundAction) (s : Atom → Bool) (s' : Atom → Bool)
    (h : I.executeB s π = some s') : I.Execution (toState s) π (toState s') := by
  induction π generalizing s with
  | nil =>
    simp only [executeB, Option.some.injEq] at h
    subst h
    exact Execution.nil _
  | cons ga π ih =>
    simp only [executeB] at h
    split at h
    · rename_i happ
      refine Execution.cons ((applicableB_iff hwf ga s).1 happ) ?_
      rw [← toState_resultB hwf]
      exact ih _ h
    · exact absurd h (by simp)

theorem executeB_complete {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    (π : List GroundAction) (s : Atom → Bool) (t : State)
    (h : I.Execution (toState s) π t) : ∃ s', I.executeB s π = some s' ∧ toState s' = t := by
  induction π generalizing s with
  | nil =>
    cases h
    exact ⟨s, rfl, rfl⟩
  | cons ga π ih =>
    cases h with
    | cons happ hrest =>
      have happ' : I.applicableB ga s = true := (applicableB_iff hwf ga s).2 happ
      rw [← toState_resultB hwf] at hrest
      obtain ⟨s', h₁, h₂⟩ := ih _ hrest
      exact ⟨s', by simp [executeB, happ', h₁], h₂⟩

/-- Executable plan validation: is `π` a plan for the instance `I`? -/
def validPlanB (I : Instance) (π : List GroundAction) : Bool :=
  match I.executeB I.initStateB π with
  | some s => Formula.evalB I Assign.id s I.problem.goal
  | none => false

/-- The executable plan validator decides `Instance.IsPlan`: it accepts exactly the
sequences of ground actions that solve the instance. -/
theorem validPlanB_iff {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    (π : List GroundAction) : I.validPlanB π = true ↔ I.IsPlan π := by
  unfold validPlanB IsPlan
  cases h : I.executeB I.initStateB π with
  | none =>
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨t, hexec, -⟩
    rw [← toState_initStateB] at hexec
    obtain ⟨s', h₁, -⟩ := executeB_complete hwf π _ t hexec
    rw [h] at h₁
    exact absurd h₁ (by simp)
  | some s =>
    rw [Formula.evalB_iff hwf]
    constructor
    · intro hgoal
      refine ⟨toState s, ?_, hgoal⟩
      rw [← toState_initStateB]
      exact executeB_sound hwf π _ s h
    · rintro ⟨t, hexec, hgoal⟩
      rw [← toState_initStateB] at hexec
      obtain ⟨s', h₁, h₂⟩ := executeB_complete hwf π _ t hexec
      rw [h] at h₁
      cases h₁
      exact h₂ ▸ hgoal

/-! ### Executable action costs -/

/-- Executable version of `Effect.cost`. -/
def effectCostB (I : Instance) (σ : Assign) (s : Atom → Bool) : Effect → Int
  | .nil => 0
  | .add _ _ => 0
  | .del _ _ => 0
  | .conj e₁ e₂ => effectCostB I σ s e₁ + effectCostB I σ s e₂
  | .all v ty e => ((I.objectsOfTypeL ty).map (fun o => effectCostB I (σ.set v o) s e)).sum
  | .when c e => if Formula.evalB I σ s c then effectCostB I σ s e else 0
  | .incCost ne => ne.eval I σ

theorem objectsOfTypeL_eq_objectsOfType {I : Instance}
    (hwf : I.domain.typesWellFormedB = true) (ty : TypeExpr) :
    I.objectsOfTypeL ty = I.objectsOfType ty := by
  classical
  simp only [objectsOfTypeL, objectsOfType]
  apply List.filter_congr
  intro o _
  rw [Bool.eq_iff_iff, decide_eq_true_eq, hasTypeB_iff hwf]

/-- The executable cost computation agrees with the declarative one. -/
theorem effectCostB_eq {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    (s : Atom → Bool) (e : Effect) (σ : Assign) :
    I.effectCostB σ s e = Effect.cost I σ (toState s) e := by
  induction e generalizing σ with
  | nil => rfl
  | add p args => rfl
  | del p args => rfl
  | conj e₁ e₂ ih₁ ih₂ => simp [effectCostB, Effect.cost, ih₁, ih₂]
  | all v ty e ih =>
    simp only [effectCostB, Effect.cost, objectsOfTypeL_eq_objectsOfType hwf]
    congr 1
    exact List.map_congr_left (fun o _ => ih _)
  | when c e ih =>
    by_cases hc : Formula.evalB I σ s c = true
    · have hc' : Formula.Holds I σ (toState s) c := (Formula.evalB_iff hwf s c σ).1 hc
      simp [effectCostB, Effect.cost, hc, hc', ih]
    · have hc' : ¬ Formula.Holds I σ (toState s) c := fun h =>
        hc ((Formula.evalB_iff hwf s c σ).2 h)
      simp [effectCostB, Effect.cost, hc, hc']
  | incCost ne => rfl

/-- Executable version of `Instance.actionCost`. -/
def actionCostB (I : Instance) (ga : GroundAction) (s : Atom → Bool) : Int :=
  match I.domain.findAction ga.name with
  | some a =>
      if I.domain.functions.any (fun f => f.name == "total-cost") then
        I.effectCostB (bind a.params ga.args) s a.eff
      else 1
  | none => 0

theorem actionCostB_eq {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    (ga : GroundAction) (s : Atom → Bool) :
    I.actionCostB ga s = I.actionCost ga (toState s) := by
  unfold actionCostB actionCost
  cases I.domain.findAction ga.name with
  | none => rfl
  | some a =>
    by_cases hf : I.domain.functions.any (fun f => f.name == "total-cost") = true
    · simp [hf, effectCostB_eq hwf]
    · simp [hf]

/-- Executable version of `Instance.trajectoryCost`. -/
def trajectoryCostB (I : Instance) (s : Atom → Bool) : List GroundAction → Int
  | [] => 0
  | ga :: π => I.actionCostB ga s + I.trajectoryCostB (I.resultB ga s) π

theorem trajectoryCostB_eq {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    (π : List GroundAction) (s : Atom → Bool) :
    I.trajectoryCostB s π = I.trajectoryCost (toState s) π := by
  induction π generalizing s with
  | nil => rfl
  | cons ga π ih =>
    simp only [trajectoryCostB, trajectoryCost, actionCostB_eq hwf, ih,
      toState_resultB hwf]

/-- Executable version of `Instance.planCost`. -/
def planCostB (I : Instance) (π : List GroundAction) : Int :=
  I.trajectoryCostB I.initStateB π

theorem planCostB_eq {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    (π : List GroundAction) : I.planCostB π = I.planCost π := by
  unfold planCostB planCost
  rw [trajectoryCostB_eq hwf, toState_initStateB]

end Instance

end PDDL
