import pddl.Ast
import Mathlib.Data.Set.Lattice
import Mathlib.Logic.Relation
import Mathlib.Data.List.Forall2
import Mathlib.Tactic

/-!
# Lifted semantics of PDDL

This module gives a formal semantics to the PDDL fragment whose syntax is defined in
`pddl.Ast`.  The semantics is *lifted*, i.e. it is defined directly on the schematic
(variable-containing) domain description, without grounding it first.

## Overview

* A **state** is a set of ground atoms (`State := Set Atom`).  The closed world assumption
  applies: an atom that is not in the state is false.
* A **variable assignment** `Assign` maps variable names to object names.  Formulas and
  effects are interpreted relative to an assignment, which is extended when a quantifier
  is traversed.
* `Formula.Holds` is the satisfaction relation of goal descriptions.  Quantifiers range
  over the objects of the instance whose declared type is a subtype of the quantifier's
  type.
* `Effect.addSet` / `Effect.delSet` collect the atoms added and deleted by an effect in a
  given state, and `Effect.apply` performs the update `(s \ del) ∪ add`.  As usual (and as
  implemented by all common planning systems) additions take precedence over deletions.
* `Instance.Applicable` and `Instance.result` define the transition relation on states, and
  `Instance.Execution` its reflexive-transitive closure along a sequence of ground actions.
  `Instance.IsPlan` says that a sequence of ground actions solves the instance, and
  `Instance.planCost` gives its cost (`1` per action if the domain does not use action
  costs, see `Instance.actionCost`).
-/

namespace PDDL

/-! ### States and assignments -/

/-- A state is a set of ground atoms; atoms not in the set are false (closed world
assumption). -/
abbrev State := Set Atom

/-- A variable assignment maps variable names to object names.  Assignments are total for
convenience; only the values on the variables that are actually bound matter. -/
abbrev Assign := Name → Name

namespace Assign

/-- The assignment that maps every variable to its own name.  Used as the (irrelevant)
initial assignment for closed formulas such as the goal. -/
def id : Assign := fun x => x

/-- `σ.set v o` is `σ` updated so that the variable `v` is mapped to the object `o`. -/
def set (σ : Assign) (v : Name) (o : Name) : Assign := fun w => if w = v then o else σ w

@[simp] theorem set_same (σ : Assign) (v o : Name) : σ.set v o v = o := by simp [set]

@[simp] theorem set_other {σ : Assign} {v w o : Name} (h : w ≠ v) : σ.set v o w = σ w := by
  simp [set, h]

end Assign

namespace Term

/-- The object denoted by a term under an assignment. -/
def inst (σ : Assign) : Term → Name
  | .var v => σ v
  | .obj o => o

end Term

/-- The ground atom obtained from a predicate name and a list of terms. -/
def groundAtom (σ : Assign) (p : Name) (args : List Term) : Atom :=
  ⟨p, args.map (Term.inst σ)⟩

/-! ### Instances -/

/-- A planning instance: a domain together with a problem for that domain. -/
structure Instance where
  domain : Domain
  problem : Problem
  deriving Inhabited

namespace Domain

/-- `t` is a declared direct subtype of `u`. -/
def DirectSubtype (d : Domain) (t u : Name) : Prop := (t, u) ∈ d.types

/-- The subtype relation: the reflexive-transitive closure of the declared type edges. -/
def TypeLE (d : Domain) : Name → Name → Prop := Relation.ReflTransGen d.DirectSubtype

theorem TypeLE.refl (d : Domain) (t : Name) : d.TypeLE t t := Relation.ReflTransGen.refl

theorem TypeLE.trans {d : Domain} {t u v : Name} (h₁ : d.TypeLE t u) (h₂ : d.TypeLE u v) :
    d.TypeLE t v := Relation.ReflTransGen.trans h₁ h₂

theorem TypeLE.of_direct {d : Domain} {t u : Name} (h : d.DirectSubtype t u) : d.TypeLE t u :=
  Relation.ReflTransGen.single h

/-- Look up an action schema by name. -/
def findAction (d : Domain) (n : Name) : Option Action :=
  d.actions.find? (fun a => a.name == n)

end Domain

namespace Instance

/-- All object declarations of the instance: the domain constants and the problem
objects. -/
def objectDecls (I : Instance) : List TypedVar :=
  I.domain.constants ++ I.problem.objects

/-- All objects of the instance. -/
def objects (I : Instance) : List Name := I.objectDecls.map (·.name)

/-- The declared type of an object, if it is declared at all. -/
def typeOf (I : Instance) (o : Name) : Option TypeExpr :=
  (I.objectDecls.find? (fun d => d.name == o)).map (·.type)

/-- The object `o` is of type `te`: `o` is declared and one of its declared (primitive)
types is a subtype of one of the alternatives of `te`. -/
def HasType (I : Instance) (o : Name) (te : TypeExpr) : Prop :=
  ∃ dte, I.typeOf o = some dte ∧ ∃ dt ∈ dte.alts, ∃ t ∈ te.alts, I.domain.TypeLE dt t

theorem HasType.mem_objects {I : Instance} {o : Name} {te : TypeExpr} (h : I.HasType o te) :
    o ∈ I.objects := by
  obtain ⟨dte, hdte, -⟩ := h
  simp only [typeOf, Option.map_eq_some_iff] at hdte
  obtain ⟨d, hd, -⟩ := hdte
  have := List.find?_some hd
  have hmem := List.mem_of_find?_eq_some hd
  simp only [beq_iff_eq] at this
  simpa [objects, ← this] using List.mem_map_of_mem (f := fun d : TypedVar => d.name) hmem

/-- The value of a static function, taken from the `:init` section of the problem.
Functions that are not initialised have value `0`. -/
def funValue (I : Instance) (f : Name) (args : List Name) : Int :=
  match I.problem.init.find? (fun e => match e with
      | .funAssign g gargs _ => g == f && gargs == args
      | .atom _ _ => false) with
  | some (.funAssign _ _ v) => v
  | _ => 0

/-- The initial state: exactly the atoms listed in the `:init` section. -/
def initState (I : Instance) : State :=
  {a : Atom | InitEl.atom a.pred a.args ∈ I.problem.init}

end Instance

/-! ### Semantics of goal descriptions -/

namespace Formula

/-- Satisfaction of a goal description in a state, under a variable assignment. -/
def Holds (I : Instance) (σ : Assign) (s : State) : Formula → Prop
  | .top => True
  | .bot => False
  | .atom p args => groundAtom σ p args ∈ s
  | .eq t₁ t₂ => t₁.inst σ = t₂.inst σ
  | .neg f => ¬ Holds I σ s f
  | .conj f g => Holds I σ s f ∧ Holds I σ s g
  | .disj f g => Holds I σ s f ∨ Holds I σ s g
  | .imp f g => Holds I σ s f → Holds I σ s g
  | .all v ty f => ∀ o, I.HasType o ty → Holds I (σ.set v o) s f
  | .ex v ty f => ∃ o, I.HasType o ty ∧ Holds I (σ.set v o) s f

@[simp] theorem holds_top {I σ s} : Holds I σ s .top := trivial
@[simp] theorem holds_bot {I σ s} : ¬ Holds I σ s .bot := id
@[simp] theorem holds_atom {I σ s p args} :
    Holds I σ s (.atom p args) ↔ groundAtom σ p args ∈ s := Iff.rfl
@[simp] theorem holds_eq {I σ s t₁ t₂} :
    Holds I σ s (.eq t₁ t₂) ↔ t₁.inst σ = t₂.inst σ := Iff.rfl
@[simp] theorem holds_neg {I σ s f} : Holds I σ s (.neg f) ↔ ¬ Holds I σ s f := Iff.rfl
@[simp] theorem holds_conj {I σ s f g} :
    Holds I σ s (.conj f g) ↔ Holds I σ s f ∧ Holds I σ s g := Iff.rfl
@[simp] theorem holds_disj {I σ s f g} :
    Holds I σ s (.disj f g) ↔ Holds I σ s f ∨ Holds I σ s g := Iff.rfl
@[simp] theorem holds_imp {I σ s f g} :
    Holds I σ s (.imp f g) ↔ (Holds I σ s f → Holds I σ s g) := Iff.rfl
@[simp] theorem holds_all {I σ s v ty f} :
    Holds I σ s (.all v ty f) ↔ ∀ o, I.HasType o ty → Holds I (σ.set v o) s f := Iff.rfl
@[simp] theorem holds_ex {I σ s v ty f} :
    Holds I σ s (.ex v ty f) ↔ ∃ o, I.HasType o ty ∧ Holds I (σ.set v o) s f := Iff.rfl

/-- The desugaring of `(and f₁ … fₙ)` performed by the parser is semantically correct. -/
theorem holds_conjList {I σ s} (fs : List Formula) :
    Holds I σ s (conjList fs) ↔ ∀ f ∈ fs, Holds I σ s f := by
  induction fs with
  | nil => simp [conjList]
  | cons f fs ih =>
    cases fs with
    | nil => simp [conjList]
    | cons g gs => simpa [conjList] using and_congr_right (fun _ => ih)

/-- The desugaring of `(or f₁ … fₙ)` performed by the parser is semantically correct. -/
theorem holds_disjList {I σ s} (fs : List Formula) :
    Holds I σ s (disjList fs) ↔ ∃ f ∈ fs, Holds I σ s f := by
  induction fs with
  | nil => simp [disjList]
  | cons f fs ih =>
    cases fs with
    | nil => simp [disjList]
    | cons g gs => simpa [disjList] using or_congr_right ih

/-- The desugaring of `(forall (?v₁ … ?vₙ) f)` performed by the parser is semantically
correct. -/
theorem holds_allList {I s} (vs : List TypedVar) (f : Formula) (σ : Assign) :
    Holds I σ s (allList vs f) ↔
      ∀ os : List Name, List.Forall₂ (fun (v : TypedVar) o => I.HasType o v.type) vs os →
        Holds I (vs.zip os |>.foldl (fun τ p => τ.set p.1.name p.2) σ) s f := by
  induction vs generalizing σ with
  | nil =>
    constructor
    · intro h os hos
      cases hos
      exact h
    · intro h
      exact h [] List.Forall₂.nil
  | cons v vs ih =>
    simp only [allList, holds_all]
    constructor
    · intro h os hos
      cases hos with
      | cons hv hvs => exact (ih _).1 (h _ hv) _ hvs
    · intro h o ho
      refine (ih _).2 (fun os hos => ?_)
      exact h (o :: os) (List.Forall₂.cons ho hos)

end Formula

/-! ### Semantics of effects -/

namespace Effect

/-- The set of atoms added by an effect, evaluated in the state `s`. -/
def addSet (I : Instance) (σ : Assign) (s : State) : Effect → Set Atom
  | .nil => ∅
  | .add p args => {groundAtom σ p args}
  | .del _ _ => ∅
  | .conj e₁ e₂ => addSet I σ s e₁ ∪ addSet I σ s e₂
  | .all v ty e => {a | ∃ o, I.HasType o ty ∧ a ∈ addSet I (σ.set v o) s e}
  | .when c e => {a | Formula.Holds I σ s c ∧ a ∈ addSet I σ s e}
  | .incCost _ => ∅

/-- The set of atoms deleted by an effect, evaluated in the state `s`. -/
def delSet (I : Instance) (σ : Assign) (s : State) : Effect → Set Atom
  | .nil => ∅
  | .add _ _ => ∅
  | .del p args => {groundAtom σ p args}
  | .conj e₁ e₂ => delSet I σ s e₁ ∪ delSet I σ s e₂
  | .all v ty e => {a | ∃ o, I.HasType o ty ∧ a ∈ delSet I (σ.set v o) s e}
  | .when c e => {a | Formula.Holds I σ s c ∧ a ∈ delSet I σ s e}
  | .incCost _ => ∅

/-- The state resulting from applying an effect: delete first, then add.  Hence an atom
that is both added and deleted by the same effect ends up being true. -/
def apply (I : Instance) (σ : Assign) (s : State) (e : Effect) : State :=
  (s \ delSet I σ s e) ∪ addSet I σ s e

theorem mem_apply {I σ s e} {a : Atom} :
    a ∈ apply I σ s e ↔ a ∈ addSet I σ s e ∨ (a ∈ s ∧ a ∉ delSet I σ s e) := by
  simp [apply, or_comm]

@[simp] theorem addSet_conjList (I : Instance) (σ : Assign) (s : State) (es : List Effect) :
    addSet I σ s (conjList es) = ⋃ e ∈ es, addSet I σ s e := by
  induction es with
  | nil => simp [conjList, addSet]
  | cons e es ih =>
    cases es with
    | nil => simp [conjList]
    | cons e' es' => simp [conjList, addSet, ih]

@[simp] theorem delSet_conjList (I : Instance) (σ : Assign) (s : State) (es : List Effect) :
    delSet I σ s (conjList es) = ⋃ e ∈ es, delSet I σ s e := by
  induction es with
  | nil => simp [conjList, delSet]
  | cons e es ih =>
    cases es with
    | nil => simp [conjList]
    | cons e' es' => simp [conjList, delSet, ih]

end Effect

/-! ### Action costs -/

namespace NumExpr

/-- The value of a cost expression.  Since only static functions may occur, the value does
not depend on the state. -/
def eval (I : Instance) (σ : Assign) : NumExpr → Int
  | .num n => n
  | .app f args => I.funValue f (args.map (Term.inst σ))

end NumExpr

namespace Instance

open Classical in
/-- The objects of a given type, as a list. -/
noncomputable def objectsOfType (I : Instance) (te : TypeExpr) : List Name :=
  I.objects.filter (fun o => decide (I.HasType o te))

theorem mem_objectsOfType {I : Instance} {te : TypeExpr} {o : Name} :
    o ∈ I.objectsOfType te ↔ o ∈ I.objects ∧ I.HasType o te := by
  classical
  simp [objectsOfType, List.mem_filter]

end Instance

namespace Effect

open Classical in
/-- The cost contributed by an effect: the sum of all `(increase (total-cost) e)`
sub-effects whose conditions hold in `s`. -/
noncomputable def cost (I : Instance) (σ : Assign) (s : State) : Effect → Int
  | .nil => 0
  | .add _ _ => 0
  | .del _ _ => 0
  | .conj e₁ e₂ => cost I σ s e₁ + cost I σ s e₂
  | .all v ty e => ((I.objectsOfType ty).map (fun o => cost I (σ.set v o) s e)).sum
  | .when c e => if Formula.Holds I σ s c then cost I σ s e else 0
  | .incCost ne => ne.eval I σ

end Effect

/-! ### Ground actions, transitions and plans -/

/-- The assignment binding the parameters of an action schema to the arguments of a ground
action.  Variables that are not parameters are mapped to themselves. -/
def bind (params : List TypedVar) (args : List Name) : Assign :=
  fun x => match ((params.map (·.name)).zip args).find? (fun p => p.1 == x) with
    | some (_, o) => o
    | none => x

namespace Instance

/-- The arguments of a ground action are type-correct for the parameters of a schema. -/
def ArgsWellTyped (I : Instance) (params : List TypedVar) (args : List Name) : Prop :=
  List.Forall₂ (fun (p : TypedVar) (o : Name) => I.HasType o p.type) params args

theorem ArgsWellTyped.length_eq {I : Instance} {params : List TypedVar} {args : List Name}
    (h : I.ArgsWellTyped params args) : params.length = args.length :=
  List.Forall₂.length_eq h

/-- A ground action is *applicable* in a state if its name refers to an action schema, its
arguments are type-correct, and its precondition holds. -/
def Applicable (I : Instance) (ga : GroundAction) (s : State) : Prop :=
  ∃ a, I.domain.findAction ga.name = some a ∧ I.ArgsWellTyped a.params ga.args ∧
    Formula.Holds I (bind a.params ga.args) s a.pre

/-- The successor state of applying a ground action.  If the action name is unknown, the
state does not change (this case never arises for applicable actions). -/
def result (I : Instance) (ga : GroundAction) (s : State) : State :=
  match I.domain.findAction ga.name with
  | some a => Effect.apply I (bind a.params ga.args) s a.eff
  | none => s

/-- The cost of applying a ground action in a state.  If the domain does not declare the
`total-cost` function (i.e. the instance does not use action costs), every action costs
`1`; otherwise the cost is the one accumulated by the `increase` effects. -/
noncomputable def actionCost (I : Instance) (ga : GroundAction) (s : State) : Int :=
  match I.domain.findAction ga.name with
  | some a =>
      if I.domain.functions.any (fun f => f.name == "total-cost") then
        Effect.cost I (bind a.params ga.args) s a.eff
      else 1
  | none => 0

/-- `Execution I s π s'` states that executing the sequence `π` of ground actions in the
state `s` is possible and leads to the state `s'`. -/
inductive Execution (I : Instance) : State → List GroundAction → State → Prop
  | nil (s : State) : Execution I s [] s
  | cons {s s' : State} {a : GroundAction} {π : List GroundAction} :
      I.Applicable a s → Execution I (I.result a s) π s' → Execution I s (a :: π) s'

/-- Executions are deterministic. -/
theorem Execution.unique {I : Instance} {s s₁ s₂ : State} {π : List GroundAction}
    (h₁ : I.Execution s π s₁) (h₂ : I.Execution s π s₂) : s₁ = s₂ := by
  induction h₁ with
  | nil s => cases h₂; rfl
  | cons _ _ ih => cases h₂ with | cons _ h => exact ih h

/-- Executions compose. -/
theorem Execution.append {I : Instance} {s₁ s₂ s₃ : State} {π₁ π₂ : List GroundAction}
    (h₁ : I.Execution s₁ π₁ s₂) (h₂ : I.Execution s₂ π₂ s₃) : I.Execution s₁ (π₁ ++ π₂) s₃ := by
  induction h₁ with
  | nil s => simpa using h₂
  | cons ha _ ih => exact Execution.cons ha (ih h₂)

/-- The goal of the instance holds in the state `s`. -/
def GoalHolds (I : Instance) (s : State) : Prop :=
  Formula.Holds I Assign.id s I.problem.goal

/-- `π` is a plan for the instance: executing it from the initial state is possible and
leads to a goal state. -/
def IsPlan (I : Instance) (π : List GroundAction) : Prop :=
  ∃ s, I.Execution I.initState π s ∧ I.GoalHolds s

/-- The cost of executing a sequence of ground actions starting in the state `s`. -/
noncomputable def trajectoryCost (I : Instance) (s : State) : List GroundAction → Int
  | [] => 0
  | a :: π => I.actionCost a s + I.trajectoryCost (I.result a s) π

/-- The cost of a plan, i.e. of executing it from the initial state. -/
noncomputable def planCost (I : Instance) (π : List GroundAction) : Int :=
  I.trajectoryCost I.initState π

/-- The state reachability relation induced by the instance. -/
def Step (I : Instance) (s s' : State) : Prop :=
  ∃ a, I.Applicable a s ∧ s' = I.result a s

/-- A state is reachable if some sequence of ground actions leads to it from the initial
state. -/
def Reachable (I : Instance) (s : State) : Prop :=
  ∃ π, I.Execution I.initState π s

theorem Reachable.initState (I : Instance) : I.Reachable I.initState :=
  ⟨[], Execution.nil _⟩

theorem Reachable.step {I : Instance} {s s' : State} (h : I.Reachable s) (hs : I.Step s s') :
    I.Reachable s' := by
  obtain ⟨π, hπ⟩ := h
  obtain ⟨a, ha, rfl⟩ := hs
  exact ⟨π ++ [a], hπ.append (Execution.cons ha (Execution.nil _))⟩

/-- Solvability of an instance. -/
def Solvable (I : Instance) : Prop := ∃ π, I.IsPlan π

end Instance

end PDDL
