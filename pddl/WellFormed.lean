import pddl.Semantics

/-!
# Well-formedness checks for parsed PDDL

Parsing only guarantees that a file is syntactically a PDDL domain/problem in the supported
fragment.  This module adds the usual *static* checks: are all predicates, functions and
types that are used also declared, do atoms have the declared arity, is every variable
bound, and are the object declarations sane?

The checks are executable and return a list of human readable error messages; an instance
is *well formed* if the list is empty.  They are independent of the semantics in
`pddl.Semantics` (which is defined for arbitrary instances) but they characterise the
instances for which that semantics behaves as a PDDL user would expect - in particular,
well-formedness is what a grounder will want to assume.
-/

namespace PDDL

namespace Domain

/-- All type names that may be used: the declared ones plus the built-in `object`. -/
def declaredTypes (d : Domain) : List Name :=
  ("object" :: typeNames d.types).eraseDups

/-- The arity of a declared predicate. -/
def predArity (d : Domain) (p : Name) : Option Nat :=
  (d.predicates.find? (fun q => q.name == p)).map (fun q => q.params.length)

/-- The arity of a declared function. -/
def funcArity (d : Domain) (f : Name) : Option Nat :=
  (d.functions.find? (fun g => g.name == f)).map (fun g => g.params.length)

end Domain

/-- Check that a type expression only mentions declared types. -/
def checkTypeExpr (d : Domain) (ctx : String) (te : TypeExpr) : List String :=
  te.alts.filterMap fun t =>
    if d.declaredTypes.contains t then none else some s!"{ctx}: undeclared type '{t}'"

/-- Check that the terms of an atom are bound variables or declared objects. -/
def checkTerms (objs : List Name) (vars : List Name) (ctx : String) (args : List Term) :
    List String :=
  args.filterMap fun
    | .var v => if vars.contains v then none else some s!"{ctx}: unbound variable '?{v}'"
    | .obj o => if objs.contains o then none else some s!"{ctx}: undeclared object '{o}'"

/-- Check an atom: the predicate must be declared with the right arity, and its arguments
must be bound variables or declared objects. -/
def checkAtomUse (d : Domain) (objs : List Name) (vars : List Name) (ctx : String)
    (p : Name) (args : List Term) : List String :=
  (match d.predArity p with
   | none => [s!"{ctx}: undeclared predicate '{p}'"]
   | some n =>
      if n = args.length then []
      else [s!"{ctx}: predicate '{p}' used with {args.length} arguments, declared with {n}"]) ++
  checkTerms objs vars ctx args

/-- Well-formedness errors of a goal description.  `vars` are the variables in scope. -/
def Formula.wfErrors (d : Domain) (objs : List Name) (ctx : String) :
    List Name → Formula → List String
  | _, .top => []
  | _, .bot => []
  | vars, .atom p args => checkAtomUse d objs vars ctx p args
  | vars, .eq t₁ t₂ => checkTerms objs vars ctx [t₁, t₂]
  | vars, .neg f => Formula.wfErrors d objs ctx vars f
  | vars, .conj f g => Formula.wfErrors d objs ctx vars f ++ Formula.wfErrors d objs ctx vars g
  | vars, .disj f g => Formula.wfErrors d objs ctx vars f ++ Formula.wfErrors d objs ctx vars g
  | vars, .imp f g => Formula.wfErrors d objs ctx vars f ++ Formula.wfErrors d objs ctx vars g
  | vars, .all v ty f =>
      checkTypeExpr d ctx ty ++ Formula.wfErrors d objs ctx (v :: vars) f
  | vars, .ex v ty f =>
      checkTypeExpr d ctx ty ++ Formula.wfErrors d objs ctx (v :: vars) f

/-- Well-formedness errors of a cost expression. -/
def NumExpr.wfErrors (d : Domain) (objs : List Name) (vars : List Name) (ctx : String) :
    NumExpr → List String
  | .num _ => []
  | .app f args =>
      (match d.funcArity f with
       | none => [s!"{ctx}: undeclared function '{f}'"]
       | some n =>
          if n = args.length then []
          else [s!"{ctx}: function '{f}' used with {args.length} arguments, declared with {n}"]) ++
      checkTerms objs vars ctx args

/-- Well-formedness errors of an effect.  `vars` are the variables in scope. -/
def Effect.wfErrors (d : Domain) (objs : List Name) (ctx : String) :
    List Name → Effect → List String
  | _, .nil => []
  | vars, .add p args => checkAtomUse d objs vars ctx p args
  | vars, .del p args => checkAtomUse d objs vars ctx p args
  | vars, .conj e₁ e₂ => Effect.wfErrors d objs ctx vars e₁ ++ Effect.wfErrors d objs ctx vars e₂
  | vars, .all v ty e => checkTypeExpr d ctx ty ++ Effect.wfErrors d objs ctx (v :: vars) e
  | vars, .when c e =>
      Formula.wfErrors d objs ctx vars c ++ Effect.wfErrors d objs ctx vars e
  | vars, .incCost ne =>
      (if d.funcArity "total-cost" = some 0 then []
       else [s!"{ctx}: 'increase (total-cost)' used but 'total-cost' is not declared"]) ++
      NumExpr.wfErrors d objs vars ctx ne

/-- Well-formedness errors of an action schema. -/
def Action.wfErrors (d : Domain) (objs : List Name) (a : Action) : List String :=
  let ctx := s!"action '{a.name}'"
  let vars := a.params.map (·.name)
  (if vars.eraseDups.length = vars.length then []
    else [s!"{ctx}: duplicate parameter names"]) ++
  a.params.flatMap (fun p => checkTypeExpr d ctx p.type) ++
  Formula.wfErrors d objs ctx vars a.pre ++
  Effect.wfErrors d objs ctx vars a.eff

namespace Domain

/-- Well-formedness errors of a domain, given the names of all objects (the domain's own
constants for a stand-alone check, plus the problem's objects when a problem is present). -/
def wfErrors (d : Domain) (objs : List Name) : List String :=
  (d.predicates.flatMap fun p =>
    p.params.flatMap (checkTypeExpr d s!"predicate '{p.name}'" ·.type)) ++
  (d.functions.flatMap fun f =>
    f.params.flatMap (checkTypeExpr d s!"function '{f.name}'" ·.type)) ++
  (d.constants.flatMap fun c => checkTypeExpr d s!"constant '{c.name}'" c.type) ++
  (if (d.actions.map (·.name)).eraseDups.length = d.actions.length then []
    else ["duplicate action names"]) ++
  (if (d.predicates.map (·.name)).eraseDups.length = d.predicates.length then []
    else ["duplicate predicate names"]) ++
  d.actions.flatMap (Action.wfErrors d objs)

end Domain

namespace Instance

/-- Well-formedness errors of an initial state element. -/
def initElWfErrors (I : Instance) (objs : List Name) : InitEl → List String
  | .atom p args =>
      checkAtomUse I.domain objs [] "init" p (args.map Term.obj)
  | .funAssign f args _ =>
      (match I.domain.funcArity f with
       | none => [s!"init: undeclared function '{f}'"]
       | some n =>
          if n = args.length then []
          else [s!"init: function '{f}' used with {args.length} arguments, declared with {n}"]) ++
      checkTerms objs [] "init" (args.map Term.obj)

/-- Well-formedness errors of a planning instance. -/
def wfErrors (I : Instance) : List String :=
  let objs := I.objects
  (if I.problem.domain == I.domain.name then []
    else [s!"problem refers to domain '{I.problem.domain}', but the domain is " ++
          s!"'{I.domain.name}'"]) ++
  (if objs.eraseDups.length = objs.length then [] else ["duplicate object names"]) ++
  I.domain.wfErrors objs ++
  (I.objectDecls.flatMap fun o => checkTypeExpr I.domain s!"object '{o.name}'" o.type) ++
  (I.problem.init.flatMap (I.initElWfErrors objs)) ++
  Formula.wfErrors I.domain objs "goal" [] I.problem.goal

/-- An instance is well formed if all static checks pass. -/
def WellFormed (I : Instance) : Prop := I.wfErrors = []

instance (I : Instance) : Decidable I.WellFormed := by
  unfold WellFormed; infer_instance

end Instance

end PDDL
