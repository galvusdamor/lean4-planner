import pddl.Ast

/-!
# Printing the PDDL abstract syntax back to concrete syntax

The printer is the inverse of the parser in the sense that

```
parseDomain (Domain.print d) = .ok d      and      parseProblem (Problem.print p) = .ok p
```

for every domain/problem produced by the parser.  This is used by the `pddlparse`
executable to check the parser by round-tripping benchmark files: a file is parsed,
printed, parsed again, and the two abstract syntax trees are compared.
-/

namespace PDDL

/-- Print a type expression. -/
def TypeExpr.print : TypeExpr → String
  | ⟨[]⟩ => "object"
  | ⟨[t]⟩ => t
  | ⟨ts⟩ => "(either " ++ String.intercalate " " ts ++ ")"

/-- Print a typed list of variables, e.g. an action parameter list. -/
def printTypedVars (vs : List TypedVar) : String :=
  String.intercalate " " (vs.map (fun v => "?" ++ v.name ++ " - " ++ v.type.print))

/-- Print a typed list of names, e.g. an object declaration. -/
def printTypedNames (vs : List TypedVar) : String :=
  String.intercalate " " (vs.map (fun v => v.name ++ " - " ++ v.type.print))

/-- Print a list of terms. -/
def printTerms (ts : List Term) : String :=
  String.intercalate " " (ts.map Term.toString)

/-- Print an atom `(p t₁ … tₙ)`. -/
def printAtomExpr (p : Name) (args : List Term) : String :=
  if args.isEmpty then "(" ++ p ++ ")" else "(" ++ p ++ " " ++ printTerms args ++ ")"

/-- Print a numeric expression. -/
def NumExpr.print : NumExpr → String
  | .num n => ToString.toString n
  | .app f args => printAtomExpr f args

/-- Print a goal description. -/
def Formula.print : Formula → String
  | .top => "(and)"
  | .bot => "(or)"
  | .atom p args => printAtomExpr p args
  | .eq t₁ t₂ => "(= " ++ t₁.toString ++ " " ++ t₂.toString ++ ")"
  | .neg f => "(not " ++ f.print ++ ")"
  | .conj f g => "(and " ++ f.print ++ " " ++ g.print ++ ")"
  | .disj f g => "(or " ++ f.print ++ " " ++ g.print ++ ")"
  | .imp f g => "(imply " ++ f.print ++ " " ++ g.print ++ ")"
  | .all v ty f => "(forall (?" ++ v ++ " - " ++ ty.print ++ ") " ++ f.print ++ ")"
  | .ex v ty f => "(exists (?" ++ v ++ " - " ++ ty.print ++ ") " ++ f.print ++ ")"

/-- Print an effect. -/
def Effect.print : Effect → String
  | .nil => "(and)"
  | .add p args => printAtomExpr p args
  | .del p args => "(not " ++ printAtomExpr p args ++ ")"
  | .conj e₁ e₂ => "(and " ++ e₁.print ++ " " ++ e₂.print ++ ")"
  | .all v ty e => "(forall (?" ++ v ++ " - " ++ ty.print ++ ") " ++ e.print ++ ")"
  | .when c e => "(when " ++ c.print ++ " " ++ e.print ++ ")"
  | .incCost ne => "(increase (total-cost) " ++ ne.print ++ ")"

/-- Print an action schema. -/
def Action.print (a : Action) : String :=
  "(:action " ++ a.name ++ "\n   :parameters (" ++ printTypedVars a.params ++ ")\n" ++
  "   :precondition " ++ a.pre.print ++ "\n   :effect " ++ a.eff.print ++ ")"

/-- Print a predicate declaration. -/
def PredicateDecl.print (p : PredicateDecl) : String :=
  "(" ++ p.name ++ (if p.params.isEmpty then "" else " " ++ printTypedVars p.params) ++ ")"

/-- Print a function declaration (always with result type `number`). -/
def FunctionDecl.print (f : FunctionDecl) : String :=
  "(" ++ f.name ++ (if f.params.isEmpty then "" else " " ++ printTypedVars f.params) ++
    ") - number"

/-- Print a domain. -/
def Domain.print (d : Domain) : String :=
  "(define (domain " ++ d.name ++ ")\n" ++
  "(:requirements " ++ String.intercalate " " d.requirements ++ ")\n" ++
  (if d.types.isEmpty then "" else
    "(:types " ++ String.intercalate " "
      (d.types.map (fun e => e.1 ++ " - " ++ e.2)) ++ ")\n") ++
  (if d.constants.isEmpty then "" else
    "(:constants " ++ printTypedNames d.constants ++ ")\n") ++
  "(:predicates " ++ String.intercalate " " (d.predicates.map PredicateDecl.print) ++ ")\n" ++
  (if d.functions.isEmpty then "" else
    "(:functions " ++ String.intercalate " " (d.functions.map FunctionDecl.print) ++ ")\n") ++
  String.intercalate "\n" (d.actions.map Action.print) ++ "\n)"

/-- Print an element of the initial state. -/
def InitEl.print : InitEl → String
  | .atom p args =>
      if args.isEmpty then "(" ++ p ++ ")" else "(" ++ p ++ " " ++ String.intercalate " " args ++ ")"
  | .funAssign f args v =>
      "(= (" ++ f ++ (if args.isEmpty then "" else " " ++ String.intercalate " " args) ++ ") " ++
        ToString.toString v ++ ")"

/-- Print a problem. -/
def Problem.print (p : Problem) : String :=
  "(define (problem " ++ p.name ++ ")\n" ++
  "(:domain " ++ p.domain ++ ")\n" ++
  "(:requirements " ++ String.intercalate " " p.requirements ++ ")\n" ++
  (if p.objects.isEmpty then "" else "(:objects " ++ printTypedNames p.objects ++ ")\n") ++
  "(:init " ++ String.intercalate " " (p.init.map InitEl.print) ++ ")\n" ++
  "(:goal " ++ p.goal.print ++ ")\n" ++
  (if p.minimizeTotalCost then "(:metric minimize (total-cost))\n" else "") ++
  ")"

end PDDL
