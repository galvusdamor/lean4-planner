import pddl.Ast
import pddl.Sexp

/-!
# A parser for PDDL domain and problem files

This module turns the s-expressions produced by `pddl.Sexp` into the abstract syntax of
`pddl.Ast`.  The grammar follows the BNF of PDDL 3.1, restricted to the fragment described
in `pddl.Ast`; every construct outside of that fragment is rejected with an error message
instead of being silently ignored.
-/

namespace PDDL

/-- The parser monad: parsing either succeeds or fails with a message. -/
abbrev ParseM := Except String

/-- Fail with the given message. -/
def perr {α : Type} (msg : String) : ParseM α := .error msg

/-! ### Basic tokens -/

/-- Parse an integer literal.  Decimal notation is accepted as long as the fractional part
is zero, since costs must be integral. -/
def parseInt (s : String) : ParseM Int :=
  match s.toInt? with
  | some n => .ok n
  | none =>
    match s.splitOn "." with
    | [a, b] =>
      match a.toInt? with
      | some n =>
        if b.all (· = '0') then .ok n
        else perr s!"non-integral number '{s}' is not supported"
      | none => perr s!"'{s}' is not a number"
    | _ => perr s!"'{s}' is not a number"

/-- Is `s` a variable name, i.e. does it start with `?`? -/
def isVarName (s : String) : Bool := s.startsWith "?"

/-- Parse a variable `?x`, returning the name without the leading `?`. -/
def parseVar : Sexp → ParseM Name
  | .atom s => if isVarName s then .ok (s.drop 1).toString else perr s!"expected a variable, got '{s}'"
  | e => perr s!"expected a variable, got '{e}'"

/-- Parse a plain name (a type, object or constant name). -/
def parseName : Sexp → ParseM Name
  | .atom s =>
      if isVarName s then perr s!"expected a name, got the variable '{s}'"
      else .ok s
  | e => perr s!"expected a name, got '{e}'"

/-- Parse a term: `?x` is a variable, any other name is an object constant. -/
def parseTerm : Sexp → ParseM Term
  | .atom s => .ok (if isVarName s then .var (s.drop 1).toString else .obj s)
  | e => perr s!"expected a term, got '{e}'"

/-- Parse a type expression: a primitive type or `(either t₁ … tₙ)`. -/
def parseTypeExpr : Sexp → ParseM TypeExpr
  | .atom s => .ok (TypeExpr.prim s)
  | .node (.atom "either" :: alts) => do
      let alts ← alts.mapM parseName
      if alts.isEmpty then perr "'(either)' needs at least one type" else .ok ⟨alts⟩
  | e => perr s!"expected a type, got '{e}'"

/-! ### Typed lists

A typed list `x₁ … xₙ - t  y₁ … yₘ - u  z₁ … z_k` assigns the type `t` to the `xᵢ`, `u` to
the `yᵢ` and the default type `object` to the `zᵢ`. -/

/-- Worker for `parseTypedList`; `pending` collects the items whose type has not been read
yet, in reverse order. -/
private def typedListAux {α : Type} (item : Sexp → ParseM α) :
    List Sexp → List α → ParseM (List (α × TypeExpr))
  | [], pending => .ok (pending.reverse.map (fun x => (x, TypeExpr.object)))
  | [.atom "-"], _ => perr "expected a type after '-'"
  | .atom "-" :: tyS :: rest, pending => do
      let ty ← parseTypeExpr tyS
      let here := pending.reverse.map (fun x => (x, ty))
      let tl ← typedListAux item rest []
      .ok (here ++ tl)
  | s :: rest, pending => do
      let x ← item s
      typedListAux item rest (x :: pending)

/-- Parse a typed list whose items are parsed by `item`. -/
def parseTypedList {α : Type} (item : Sexp → ParseM α) (xs : List Sexp) :
    ParseM (List (α × TypeExpr)) :=
  typedListAux item xs []

/-- Parse a typed list of variables, e.g. an action parameter list. -/
def parseTypedVars (xs : List Sexp) : ParseM (List TypedVar) := do
  let l ← parseTypedList parseVar xs
  .ok (l.map (fun (n, t) => ⟨n, t⟩))

/-- Parse a typed list of names, e.g. an object or constant declaration. -/
def parseTypedNames (xs : List Sexp) : ParseM (List TypedVar) := do
  let l ← parseTypedList parseName xs
  .ok (l.map (fun (n, t) => ⟨n, t⟩))

/-! ### Goal descriptions -/

/-- Parse a quantifier prefix `(?x - t ?y - u)`. -/
private def parseBinders : Sexp → ParseM (List TypedVar)
  | .node xs => parseTypedVars xs
  | e => perr s!"expected a list of variables, got '{e}'"

/-- Parse a goal description (`<GD>`), i.e. a formula usable as a precondition or goal. -/
def parseFormula : Sexp → ParseM Formula
  | .atom s => perr s!"expected a formula, got the atom '{s}'"
  | .node [] => .ok .top
  | .node (.atom "and" :: fs) => do
      let fs ← fs.attach.mapM (fun ⟨f, _⟩ => parseFormula f)
      .ok (Formula.conjList fs)
  | .node (.atom "or" :: fs) => do
      let fs ← fs.attach.mapM (fun ⟨f, _⟩ => parseFormula f)
      .ok (Formula.disjList fs)
  | .node [.atom "not", f] => do
      let f ← parseFormula f
      .ok (.neg f)
  | .node [.atom "imply", f, g] => do
      let f ← parseFormula f
      let g ← parseFormula g
      .ok (.imp f g)
  | .node [.atom "forall", bs, f] => do
      let vs ← parseBinders bs
      let f ← parseFormula f
      .ok (Formula.allList vs f)
  | .node [.atom "exists", bs, f] => do
      let vs ← parseBinders bs
      let f ← parseFormula f
      .ok (Formula.exList vs f)
  | .node [.atom "=", t₁, t₂] => do
      let t₁ ← parseTerm t₁
      let t₂ ← parseTerm t₂
      .ok (.eq t₁ t₂)
  | .node (.atom "preference" :: _) =>
      perr "preferences are not supported"
  | .node (.atom p :: args) =>
      if p == "not" || p == "imply" || p == "forall" || p == "exists" || p == "=" then
        perr s!"malformed '{p}' formula"
      else if p == "<" || p == ">" || p == "<=" || p == ">=" then
        perr "numeric comparisons are not supported"
      else do
        let args ← args.mapM parseTerm
        .ok (.atom p args)
  | e => perr s!"expected a formula, got '{e}'"

/-! ### Effects -/

/-- Parse the numeric expression of an `(increase (total-cost) …)` effect. -/
def parseNumExpr : Sexp → ParseM NumExpr
  | .atom s => do
      let n ← parseInt s
      .ok (.num n)
  | .node (.atom f :: args) => do
      let args ← args.mapM parseTerm
      .ok (.app f args)
  | e => perr s!"expected a numeric expression, got '{e}'"

/-- Is this s-expression the total-cost fluent `(total-cost)`? -/
private def isTotalCost : Sexp → Bool
  | .node [.atom "total-cost"] => true
  | _ => false

/-- Parse an effect. -/
def parseEffect : Sexp → ParseM Effect
  | .atom s => perr s!"expected an effect, got the atom '{s}'"
  | .node [] => .ok .nil
  | .node (.atom "and" :: es) => do
      let es ← es.attach.mapM (fun ⟨e, _⟩ => parseEffect e)
      .ok (Effect.conjList es)
  | .node [.atom "forall", bs, e] => do
      let vs ← parseBinders bs
      let e ← parseEffect e
      .ok (Effect.allList vs e)
  | .node [.atom "when", c, e] => do
      let c ← parseFormula c
      let e ← parseEffect e
      .ok (.when c e)
  | .node [.atom "not", a] =>
      match a with
      | .node (.atom p :: args) => do
          let args ← args.mapM parseTerm
          .ok (.del p args)
      | e => perr s!"expected an atom after 'not', got '{e}'"
  | .node [.atom "increase", f, e] =>
      if isTotalCost f then do
        let e ← parseNumExpr e
        .ok (.incCost e)
      else
        perr s!"only '(increase (total-cost) …)' is supported, got '{f}'"
  | .node (.atom "decrease" :: _) => perr "'decrease' effects are not supported"
  | .node (.atom "assign" :: _) => perr "'assign' effects are not supported"
  | .node (.atom "scale-up" :: _) => perr "'scale-up' effects are not supported"
  | .node (.atom "scale-down" :: _) => perr "'scale-down' effects are not supported"
  | .node (.atom p :: args) =>
      if p == "not" || p == "forall" || p == "when" || p == "increase" then
        perr s!"malformed '{p}' effect"
      else do
        let args ← args.mapM parseTerm
        .ok (.add p args)
  | e => perr s!"expected an effect, got '{e}'"

/-! ### Requirements -/

/-- The requirement flags understood by this development. -/
def supportedRequirements : List Name :=
  [":strips", ":typing", ":equality", ":negative-preconditions",
   ":disjunctive-preconditions", ":existential-preconditions", ":universal-preconditions",
   ":quantified-preconditions", ":conditional-effects", ":adl", ":action-costs"]

/-- Check that all requirement flags are supported. -/
def checkRequirements (rs : List Name) : ParseM Unit :=
  match rs.find? (fun r => !supportedRequirements.contains r) with
  | some r => perr s!"unsupported requirement '{r}'"
  | none => .ok ()

/-- Parse a `(:requirements …)` section. -/
def parseRequirements (xs : List Sexp) : ParseM (List Name) := do
  let rs ← xs.mapM fun
    | .atom s => .ok s
    | e => perr s!"expected a requirement flag, got '{e}'"
  checkRequirements rs
  .ok rs

/-! ### Type hierarchy -/

/-- Parse a `(:types …)` section into a list of `(type, direct supertype)` edges. -/
def parseTypes (xs : List Sexp) : ParseM (List (Name × Name)) := do
  let l ← parseTypedList parseName xs
  let es := l.flatMap (fun (t, ty) => ty.alts.map (fun p => (t, p)))
  .ok (normalizeTypes es)

/-! ### Predicates and functions -/

/-- Parse a single predicate declaration `(p ?x - t …)`. -/
def parsePredicateDecl : Sexp → ParseM PredicateDecl
  | .node (.atom p :: args) => do
      let params ← parseTypedVars args
      .ok ⟨p, params⟩
  | e => perr s!"expected a predicate declaration, got '{e}'"

/-- Parse a `(:predicates …)` section. -/
def parsePredicates (xs : List Sexp) : ParseM (List PredicateDecl) :=
  xs.mapM parsePredicateDecl

/-- Parse a single function declaration `(f ?x - t …)`. -/
def parseFunctionDecl : Sexp → ParseM FunctionDecl
  | .node (.atom f :: args) => do
      let params ← parseTypedVars args
      .ok ⟨f, params⟩
  | e => perr s!"expected a function declaration, got '{e}'"

/-- Parse a `(:functions …)` section.  The declared result types have to be `number`. -/
def parseFunctions (xs : List Sexp) : ParseM (List FunctionDecl) := do
  let l ← parseTypedList parseFunctionDecl xs
  l.mapM fun (d, ty) =>
    if ty.alts == ["number"] || ty.alts == ["object"] then .ok d
    else perr s!"function '{d.name}' has non-numeric result type"

/-! ### Actions -/

/-- Parse the keyword arguments of an `(:action …)` section. -/
private def parseActionFields (name : Name) :
    List Sexp → Option (List TypedVar) → Option Formula → Option Effect → ParseM Action
  | [], params, pre, eff =>
      .ok ⟨name, params.getD [], pre.getD .top, eff.getD .nil⟩
  | .atom ":parameters" :: ps :: rest, _, pre, eff => do
      let vs ← parseBinders ps
      parseActionFields name rest (some vs) pre eff
  | .atom ":precondition" :: p :: rest, params, _, eff => do
      let f ← parseFormula p
      parseActionFields name rest params (some f) eff
  | .atom ":effect" :: e :: rest, params, pre, _ => do
      let ef ← parseEffect e
      parseActionFields name rest params pre (some ef)
  | .atom k :: _, _, _, _ => perr s!"unsupported field '{k}' in action '{name}'"
  | e :: _, _, _, _ => perr s!"unexpected '{e}' in action '{name}'"

/-- Parse an `(:action …)` section. -/
def parseAction : List Sexp → ParseM Action
  | .atom name :: rest => parseActionFields name rest none none none
  | _ => perr "expected an action name"

/-! ### Domains -/

/-- Parse the sections of a domain, accumulating into `d`. -/
private def parseDomainSections (d : Domain) : List Sexp → ParseM Domain
  | [] => .ok d
  | .node (.atom ":requirements" :: rs) :: rest => do
      let rs ← parseRequirements rs
      parseDomainSections { d with requirements := rs } rest
  | .node (.atom ":types" :: ts) :: rest => do
      let ts ← parseTypes ts
      parseDomainSections { d with types := ts } rest
  | .node (.atom ":constants" :: cs) :: rest => do
      let cs ← parseTypedNames cs
      parseDomainSections { d with constants := cs } rest
  | .node (.atom ":predicates" :: ps) :: rest => do
      let ps ← parsePredicates ps
      parseDomainSections { d with predicates := ps } rest
  | .node (.atom ":functions" :: fs) :: rest => do
      let fs ← parseFunctions fs
      parseDomainSections { d with functions := fs } rest
  | .node (.atom ":action" :: a) :: rest => do
      let a ← parseAction a
      parseDomainSections { d with actions := d.actions ++ [a] } rest
  | .node (.atom ":durative-action" :: _) :: _ =>
      perr "durative actions are not supported"
  | .node (.atom ":derived" :: _) :: _ =>
      perr "derived predicates are not supported"
  | .node (.atom ":constraints" :: _) :: _ =>
      perr "constraints are not supported"
  | .node (.atom k :: _) :: _ => perr s!"unsupported domain section '{k}'"
  | e :: _ => perr s!"unexpected '{e}' in domain"

/-- The empty domain, used as the starting point of `parseDomainSections`. -/
def emptyDomain (name : Name) : Domain :=
  { name, requirements := [], types := normalizeTypes [], constants := [],
    predicates := [], functions := [], actions := [] }

/-- Parse a domain from its s-expression. -/
def parseDomainSexp : Sexp → ParseM Domain
  | .node (.atom "define" :: .node [.atom "domain", .atom name] :: rest) =>
      parseDomainSections (emptyDomain name) rest
  | _ => perr "expected '(define (domain <name>) …)'"

/-- Parse a domain from the contents of a PDDL domain file. -/
def parseDomain (s : String) : ParseM Domain := do
  parseDomainSexp (← parseSexp s)

/-! ### Problems -/

/-- Parse an element of the `(:init …)` section. -/
def parseInitEl : Sexp → ParseM InitEl
  | .node [.atom "=", .node (.atom f :: args), .atom v] => do
      let args ← args.mapM parseName
      let v ← parseInt v
      .ok (.funAssign f args v)
  | .node (.atom "=" :: _) => perr "malformed function initialisation in ':init'"
  | .node (.atom "not" :: _) =>
      perr "negative literals in ':init' are not supported (the closed world assumption applies)"
  | .node (.atom p :: args) =>
      -- `(at <number> …)` is a timed initial literal, which is out of scope.
      if p == "at" then
        match args with
        | .atom t :: _ :: _ =>
            if t != "" && t.toList.all (fun c => c.isDigit || c = '.') then
              perr "timed initial literals are not supported"
            else do
              let args ← args.mapM parseName
              .ok (.atom p args)
        | _ => do
            let args ← args.mapM parseName
            .ok (.atom p args)
      else do
        let args ← args.mapM parseName
        .ok (.atom p args)
  | e => perr s!"expected an initial state element, got '{e}'"

/-- Parse a `(:metric …)` section; only `(:metric minimize (total-cost))` is supported. -/
def parseMetric : List Sexp → ParseM Bool
  | [.atom "minimize", e] =>
      if isTotalCost e then .ok true
      else perr s!"only '(:metric minimize (total-cost))' is supported, got '{e}'"
  | _ => perr "only '(:metric minimize (total-cost))' is supported"

/-- Parse the sections of a problem, accumulating into `p`. -/
private def parseProblemSections (p : Problem) : List Sexp → ParseM Problem
  | [] => .ok p
  | .node [.atom ":domain", .atom d] :: rest =>
      parseProblemSections { p with domain := d } rest
  | .node (.atom ":requirements" :: rs) :: rest => do
      let rs ← parseRequirements rs
      parseProblemSections { p with requirements := rs } rest
  | .node (.atom ":objects" :: os) :: rest => do
      let os ← parseTypedNames os
      parseProblemSections { p with objects := os } rest
  | .node (.atom ":init" :: is) :: rest => do
      let is ← is.mapM parseInitEl
      parseProblemSections { p with init := is } rest
  | .node [.atom ":goal", g] :: rest => do
      let g ← parseFormula g
      parseProblemSections { p with goal := g } rest
  | .node (.atom ":metric" :: m) :: rest => do
      let b ← parseMetric m
      parseProblemSections { p with minimizeTotalCost := b } rest
  | .node (.atom ":constraints" :: _) :: _ => perr "constraints are not supported"
  | .node (.atom k :: _) :: _ => perr s!"unsupported problem section '{k}'"
  | e :: _ => perr s!"unexpected '{e}' in problem"

/-- The empty problem, used as the starting point of `parseProblemSections`. -/
def emptyProblem (name : Name) : Problem :=
  { name, domain := "", requirements := [], objects := [], init := [], goal := .top,
    minimizeTotalCost := false }

/-- Parse a problem from its s-expression. -/
def parseProblemSexp : Sexp → ParseM Problem
  | .node (.atom "define" :: .node [.atom "problem", .atom name] :: rest) =>
      parseProblemSections (emptyProblem name) rest
  | _ => perr "expected '(define (problem <name>) …)'"

/-- Parse a problem from the contents of a PDDL problem file. -/
def parseProblem (s : String) : ParseM Problem := do
  parseProblemSexp (← parseSexp s)

/-- The result of parsing a PDDL file whose kind is not known in advance. -/
inductive DomainOrProblem where
  | dom (d : Domain)
  | prob (p : Problem)

/-- Parse a PDDL file that is either a domain or a problem file. -/
def parseDomainOrProblem (s : String) : ParseM DomainOrProblem := do
  match ← parseSexp s with
  | e@(.node (.atom "define" :: .node (.atom "domain" :: _) :: _)) =>
      return .dom (← parseDomainSexp e)
  | e@(.node (.atom "define" :: .node (.atom "problem" :: _) :: _)) =>
      return .prob (← parseProblemSexp e)
  | _ => perr "expected '(define (domain <name>) …)' or '(define (problem <name>) …)'"

end PDDL
