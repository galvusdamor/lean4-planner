import pddl.Grounding.Task
import pddl.Eval

/-!
# Naive full grounding

This module defines the grounder: given a PDDL `Instance`, it enumerates all type-correct
instantiations of every action schema, evaluates the (static parts of the) preconditions
and effects, and produces a `GroundTask`.

Lifted goal descriptions (used for preconditions, effect conditions and the goal) are
compiled into *disjunctive normal form* over ground literals (`Dnf`, see
`pddl.Grounding.Task`).  This covers the whole supported fragment:

* an atom becomes a positive literal, `(not …)` is pushed inwards by De Morgan
  (`dnfNot`), `(and …)` distributes over the disjuncts (`dnfAnd`) and `(or …)` is
  concatenation (`dnfOr`);
* equalities `(= t₁ t₂)` are decided statically — after instantiation both sides are
  objects — so `(not (= ?x ?y))` compiles to the constant `true` or `false`;
* quantifiers are expanded over the objects of their type, `forall` as a conjunction and
  `exists` as a disjunction.

A precondition with several disjuncts produces *several operators* for the same ground
action, one per disjunct; a disjunct that is statically false disappears, so an
instantiation whose precondition is unsatisfiable produces no operator at all.  Likewise a
conditional effect with a disjunctive condition produces one conditional effect per
disjunct.  The goal is kept in disjunctive normal form (`GroundTask.goal`).

The only source of failure (`none`) left is a cost effect `(increase (total-cost) …)`
below a condition that cannot be decided statically: operator costs are state independent,
so such an effect cannot be expressed and is rejected rather than mistranslated.
-/

namespace PDDL

/-! ### Enumerating type-correct instantiations -/

namespace Instance

/-- All type-correct instantiations of a parameter list. -/
def instantiations (I : Instance) : List TypedVar → List (List Name)
  | [] => [[]]
  | p :: ps =>
      -- the two lists are bound outside the lambda so that they are computed only once
      let objs := I.objectsOfTypeL p.type
      let rest := I.instantiations ps
      objs.flatMap (fun o => rest.map (fun args => o :: args))

theorem mem_instantiations_iff {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    (params : List TypedVar) (args : List Name) :
    args ∈ I.instantiations params ↔ I.ArgsWellTyped params args := by
  induction params generalizing args with
  | nil =>
    simp only [instantiations, List.mem_singleton]
    constructor
    · rintro rfl; exact List.Forall₂.nil
    · rintro h; cases h; rfl
  | cons p ps ih =>
    simp only [instantiations, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨o, ho, args', hargs', rfl⟩
      exact List.Forall₂.cons ((mem_objectsOfTypeL_iff hwf o p.type).1 ho) ((ih args').1 hargs')
    · intro h
      cases h with
      | cons hp hps =>
        rename_i o args'
        exact ⟨o, (mem_objectsOfTypeL_iff hwf o p.type).2 hp, args',
          (ih args').2 hps, rfl⟩

end Instance

/-! ### Operations on disjunctive normal forms -/

/-- The DNF that always holds: the disjunction of the empty conjunction. -/
def dnfTrue : Dnf := [[]]

/-- The DNF that never holds: the empty disjunction. -/
def dnfFalse : Dnf := []

/-- The conjunction of two DNFs, obtained by distributing. -/
def dnfAnd (d₁ d₂ : Dnf) : Dnf := d₁.flatMap (fun c₁ => d₂.map (fun c₂ => c₁ ++ c₂))

/-- The disjunction of two DNFs. -/
def dnfOr (d₁ d₂ : Dnf) : Dnf := d₁ ++ d₂

/-- The negation of a DNF: `¬ (c₁ ∨ … ∨ cₙ)` is `¬ c₁ ∧ … ∧ ¬ cₙ`, and each `¬ cᵢ` is the
disjunction of the complements of the literals of `cᵢ`; distributing gives a DNF again. -/
def dnfNot : Dnf → Dnf
  | [] => dnfTrue
  | c :: d => (dnfNot d).flatMap (fun rest => c.map (fun l => l.complement :: rest))

@[simp] theorem dnfHolds_dnfTrue (s : State) : DnfHolds dnfTrue s := by
  exact ⟨[], by simp [dnfTrue], by simp⟩

@[simp] theorem dnfHolds_dnfFalse (s : State) : ¬ DnfHolds dnfFalse s := by
  simp [dnfFalse]

@[simp] theorem dnfHolds_dnfOr {d₁ d₂ : Dnf} {s : State} :
    DnfHolds (dnfOr d₁ d₂) s ↔ DnfHolds d₁ s ∨ DnfHolds d₂ s := by
  simp [dnfOr]

@[simp] theorem dnfHolds_dnfAnd {d₁ d₂ : Dnf} {s : State} :
    DnfHolds (dnfAnd d₁ d₂) s ↔ DnfHolds d₁ s ∧ DnfHolds d₂ s := by
  simp only [dnfAnd, DnfHolds, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨c, ⟨c₁, hc₁, c₂, hc₂, rfl⟩, hc⟩
    rw [clauseHolds_append] at hc
    exact ⟨⟨c₁, hc₁, hc.1⟩, ⟨c₂, hc₂, hc.2⟩⟩
  · rintro ⟨⟨c₁, hc₁, h₁⟩, ⟨c₂, hc₂, h₂⟩⟩
    exact ⟨c₁ ++ c₂, ⟨c₁, hc₁, c₂, hc₂, rfl⟩, clauseHolds_append.2 ⟨h₁, h₂⟩⟩

@[simp] theorem dnfHolds_dnfNot {d : Dnf} {s : State} :
    DnfHolds (dnfNot d) s ↔ ¬ DnfHolds d s := by
  classical
  induction d with
  | nil => simp [dnfNot]
  | cons c d ih =>
    have hstep : DnfHolds (dnfNot (c :: d)) s ↔
        (∃ l ∈ c, ¬ l.Holds s) ∧ DnfHolds (dnfNot d) s := by
      simp only [dnfNot, DnfHolds, List.mem_flatMap, List.mem_map]
      constructor
      · rintro ⟨cl, ⟨rest, hrest, l, hl, rfl⟩, hcl⟩
        rw [clauseHolds_cons] at hcl
        exact ⟨⟨l, hl, by simpa using hcl.1⟩, ⟨rest, hrest, hcl.2⟩⟩
      · rintro ⟨⟨l, hl, hlh⟩, ⟨rest, hrest, hr⟩⟩
        refine ⟨l.complement :: rest, ⟨rest, hrest, l, hl, rfl⟩, ?_⟩
        rw [clauseHolds_cons]
        exact ⟨by simpa using hlh, hr⟩
    rw [hstep, ih, dnfHolds_cons, not_or]
    refine and_congr_left (fun _ => ?_)
    simp only [ClauseHolds, not_forall]
    constructor
    · rintro ⟨l, hl, h⟩; exact ⟨l, hl, h⟩
    · rintro ⟨l, hl, h⟩; exact ⟨l, hl, h⟩

/-- Compile a lifted goal description into disjunctive normal form, under the
instantiation `σ`.  Every formula of the supported fragment is compiled; the resulting DNF
is `dnfFalse` if the formula is statically unsatisfiable and `dnfTrue` if it is statically
valid. -/
def groundFormula (I : Instance) (σ : Assign) : Formula → Dnf
  | .top => dnfTrue
  | .bot => dnfFalse
  | .atom p args => [[.pos (groundAtom σ p args)]]
  | .eq t₁ t₂ => if t₁.inst σ = t₂.inst σ then dnfTrue else dnfFalse
  | .neg f => dnfNot (groundFormula I σ f)
  | .conj f g => dnfAnd (groundFormula I σ f) (groundFormula I σ g)
  | .disj f g => dnfOr (groundFormula I σ f) (groundFormula I σ g)
  | .imp f g => dnfOr (dnfNot (groundFormula I σ f)) (groundFormula I σ g)
  | .all v ty f =>
      (I.objectsOfTypeL ty).foldr
        (fun o acc => dnfAnd (groundFormula I (σ.set v o) f) acc) dnfTrue
  | .ex v ty f =>
      (I.objectsOfTypeL ty).foldr
        (fun o acc => dnfOr (groundFormula I (σ.set v o) f) acc) dnfFalse

/-! ### Compiling effects -/

/-- Add a list of literals to the condition of a conditional effect. -/
def CondEff.prefixCond (cs : List Lit) (ce : CondEff) : CondEff :=
  ⟨cs ++ ce.cond, ce.add, ce.del⟩

/-- Guard a list of conditional effects by a compiled condition: one copy of the effects
per disjunct of the condition. -/
def guardCondEffs (d : Dnf) (l : List CondEff) : List CondEff :=
  d.flatMap (fun c => l.map (CondEff.prefixCond c))

/-- Compile a lifted effect into a list of ground conditional effects together with the
(state independent) cost it contributes.  Returns `none` if the effect is not
expressible, which happens exactly when a nonzero cost effect occurs under a condition
that cannot be decided statically. -/
def groundEffect (I : Instance) (σ : Assign) : Effect → Option (List CondEff × Int)
  | .nil => some ([], 0)
  | .add p args => some ([⟨[], [groundAtom σ p args], []⟩], 0)
  | .del p args => some ([⟨[], [], [groundAtom σ p args]⟩], 0)
  | .conj e₁ e₂ => do
      let (l₁, c₁) ← groundEffect I σ e₁
      let (l₂, c₂) ← groundEffect I σ e₂
      pure (l₁ ++ l₂, c₁ + c₂)
  | .all v ty e =>
      (I.objectsOfTypeL ty).foldr
        (fun o acc => do
          let (l, c) ← groundEffect I (σ.set v o) e
          let (l', c') ← acc
          pure (l ++ l', c + c'))
        (some ([], 0))
  | .when cnd e => do
      let d := groundFormula I σ cnd
      let (l, cost) ← groundEffect I σ e
      if cost = 0 then
        pure (guardCondEffs d l, 0)
      else
        -- a nonzero cost may only occur under a statically decidable condition
        match d with
        | [] => pure ([], 0)
        | [[]] => pure (l, cost)
        | _ => none
  | .incCost ne => some ([], ne.eval I σ)

/-! ### Grounding action schemas -/

/-- Whether the instance uses action costs (i.e. declares the `total-cost` function). -/
def Instance.usesActionCosts (I : Instance) : Bool :=
  I.domain.functions.any (fun f => f.name == "total-cost")

/-- Ground a single instantiation of an action schema: one operator per disjunct of the
compiled precondition (so no operator at all if the precondition is statically false). -/
def groundActionInstance (I : Instance) (a : Action) (args : List Name) :
    Option (List GroundOp) := do
  let σ := bind a.params args
  let d := groundFormula I σ a.pre
  let (effs, c) ← groundEffect I σ a.eff
  pure (d.map (fun pre => ⟨⟨a.name, args⟩, pre, effs, if I.usesActionCosts then c else 1⟩))

/-- Ground a list of instantiations of one action schema. -/
def groundInstances (I : Instance) (a : Action) : List (List Name) → Option (List GroundOp)
  | [] => some []
  | args :: rest => do
      let l ← groundActionInstance I a args
      let l' ← groundInstances I a rest
      pure (l ++ l')

/-- Ground all instantiations of one action schema.  A schema that is shadowed by an
earlier schema of the same name is skipped, since it can never be referred to. -/
def groundActionSchema (I : Instance) (a : Action) : Option (List GroundOp) :=
  if I.domain.findAction a.name = some a then
    groundInstances I a (I.instantiations a.params)
  else
    some []

/-- Ground all schemas of a list of action schemas. -/
def groundSchemas (I : Instance) : List Action → Option (List GroundOp)
  | [] => some []
  | a :: as => do
      let l ← groundActionSchema I a
      let l' ← groundSchemas I as
      pure (l ++ l')

/-- All ground operators of an instance. -/
def groundOps (I : Instance) : Option (List GroundOp) :=
  groundSchemas I I.domain.actions

/-- The initial state as a list of atoms. -/
def Instance.initAtoms (I : Instance) : List Atom :=
  I.problem.init.filterMap (fun e => match e with
    | .atom p args => some ⟨p, args⟩
    | .funAssign _ _ _ => none)

theorem Instance.mem_initAtoms {I : Instance} {a : Atom} :
    a ∈ I.initAtoms ↔ InitEl.atom a.pred a.args ∈ I.problem.init := by
  simp only [initAtoms, List.mem_filterMap]
  constructor
  · rintro ⟨e, he, heq⟩
    cases e with
    | atom p args => cases heq; exact he
    | funAssign _ _ _ => exact absurd heq (by simp)
  · intro h
    exact ⟨.atom a.pred a.args, h, by simp⟩

/-- The naive full grounding of a PDDL instance.  Returns `none` only if some effect uses a
nonzero action cost below a condition that cannot be decided statically (see the module
docstring). -/
def groundInstance (I : Instance) : Option GroundTask := do
  let ops ← groundOps I
  pure ⟨ops, I.initAtoms, groundFormula I Assign.id I.problem.goal⟩

end PDDL
