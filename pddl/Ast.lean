/-!
# Abstract syntax of the supported PDDL fragment

This module defines the abstract syntax tree of the fragment of PDDL 3.1
(Gerevini & Long, *Plan Constraints and Preferences in PDDL3*, and the BNF of PDDL 3.1)
that this development supports.

Supported requirement flags are

* `:strips`, `:typing`, `:equality`,
* `:negative-preconditions`, `:disjunctive-preconditions`,
* `:existential-preconditions`, `:universal-preconditions`, `:quantified-preconditions`,
* `:conditional-effects`, `:adl` (and the historic `:adl` sub-flags),
* `:action-costs`.

Explicitly *not* supported (and rejected by the parser):
numeric fluents other than action costs, durative actions and any other temporal feature,
preferences and constraints, derived predicates, and plan metrics other than
`(:metric minimize (total-cost))`.

Note on action costs: the only numeric fluent allowed is the special `total-cost`, and the
only numeric effect allowed is `(increase (total-cost) e)` where `e` is a numeric constant
or an application of a *static* function (a function that is never modified by an action) to
the action's arguments.  This is the usual "action costs" fragment.
-/

namespace PDDL

/-- Names of predicates, types, objects and variables.  All names are stored folded to
lower case, because PDDL is case insensitive. -/
abbrev Name := String

/-- A term appearing in a lifted formula or effect: either a variable (written `?x` in
concrete syntax) or an object/constant name. -/
inductive Term where
  | var (n : Name)
  | obj (n : Name)
  deriving DecidableEq, Repr, Inhabited

namespace Term

/-- Rendering a term in concrete PDDL syntax. -/
def toString : Term → String
  | .var n => "?" ++ n
  | .obj n => n

instance : ToString Term := ⟨toString⟩

end Term

/-- A type expression, i.e. a primitive type or an `(either t₁ … tₙ)` union of primitive
types.  The list `alts` is the list of the primitive types of the union; a primitive type
`t` is represented as `⟨[t]⟩`. -/
structure TypeExpr where
  alts : List Name
  deriving DecidableEq, Repr, Inhabited

namespace TypeExpr

/-- The primitive type `t`. -/
def prim (t : Name) : TypeExpr := ⟨[t]⟩

/-- The built-in root type `object`. -/
def object : TypeExpr := prim "object"

end TypeExpr

/-- A typed variable, as used in action parameter lists and quantifiers. -/
structure TypedVar where
  name : Name
  type : TypeExpr
  deriving DecidableEq, Repr, Inhabited

/-- The declaration of a predicate: its name and its typed parameters. -/
structure PredicateDecl where
  name : Name
  params : List TypedVar
  deriving DecidableEq, Repr, Inhabited

/-- The declaration of a (static, numeric) function: its name and its typed parameters. -/
structure FunctionDecl where
  name : Name
  params : List TypedVar
  deriving DecidableEq, Repr, Inhabited

/-- A numeric expression usable as an action cost.  Since state dependent action costs are
out of scope, a cost is either an integer constant or an application of a static function
to terms (in practice: to the parameters of the action). -/
inductive NumExpr where
  | num (n : Int)
  | app (f : Name) (args : List Term)
  deriving DecidableEq, Repr, Inhabited

/-- Goal descriptions (`<GD>` in the PDDL grammar), used for preconditions and goals.

`n`-ary conjunctions and disjunctions of the concrete syntax are desugared into the binary
connectives (with `top`/`bot` for the empty case), and quantifiers over several variables
are desugared into nested single-variable quantifiers. -/
inductive Formula where
  /-- The empty conjunction `(and)`. -/
  | top
  /-- The empty disjunction `(or)`. -/
  | bot
  /-- An atom `(p t₁ … tₙ)`. -/
  | atom (p : Name) (args : List Term)
  /-- An equality `(= t₁ t₂)`. -/
  | eq (t₁ t₂ : Term)
  /-- A negation `(not f)`. -/
  | neg (f : Formula)
  /-- A conjunction `(and f g)`. -/
  | conj (f g : Formula)
  /-- A disjunction `(or f g)`. -/
  | disj (f g : Formula)
  /-- An implication `(imply f g)`. -/
  | imp (f g : Formula)
  /-- A universal quantification `(forall (?v - ty) f)`. -/
  | all (v : Name) (ty : TypeExpr) (f : Formula)
  /-- An existential quantification `(exists (?v - ty) f)`. -/
  | ex (v : Name) (ty : TypeExpr) (f : Formula)
  deriving DecidableEq, Repr, Inhabited

namespace Formula

/-- The conjunction of a list of formulas. -/
def conjList : List Formula → Formula
  | [] => .top
  | [f] => f
  | f :: fs => .conj f (conjList fs)

/-- The disjunction of a list of formulas. -/
def disjList : List Formula → Formula
  | [] => .bot
  | [f] => f
  | f :: fs => .disj f (disjList fs)

/-- Universal quantification over a list of typed variables. -/
def allList : List TypedVar → Formula → Formula
  | [], f => f
  | v :: vs, f => .all v.name v.type (allList vs f)

/-- Existential quantification over a list of typed variables. -/
def exList : List TypedVar → Formula → Formula
  | [], f => f
  | v :: vs, f => .ex v.name v.type (exList vs f)

end Formula

/-- Action effects.

`n`-ary conjunctions are desugared into the binary `conj` (with `nil` for the empty
conjunction), and `(forall (?v₁ … ?vₙ) e)` into nested single-variable quantifiers. -/
inductive Effect where
  /-- The empty effect `(and)`. -/
  | nil
  /-- Make the atom `(p t₁ … tₙ)` true. -/
  | add (p : Name) (args : List Term)
  /-- Make the atom `(p t₁ … tₙ)` false, i.e. `(not (p t₁ … tₙ))`. -/
  | del (p : Name) (args : List Term)
  /-- The conjunction of two effects. -/
  | conj (e₁ e₂ : Effect)
  /-- A universally quantified effect `(forall (?v - ty) e)`. -/
  | all (v : Name) (ty : TypeExpr) (e : Effect)
  /-- A conditional effect `(when c e)`. -/
  | when (c : Formula) (e : Effect)
  /-- The cost effect `(increase (total-cost) e)`. -/
  | incCost (e : NumExpr)
  deriving DecidableEq, Repr, Inhabited

namespace Effect

/-- The conjunction of a list of effects. -/
def conjList : List Effect → Effect
  | [] => .nil
  | [e] => e
  | e :: es => .conj e (conjList es)

/-- Universally quantified effect over a list of typed variables. -/
def allList : List TypedVar → Effect → Effect
  | [], e => e
  | v :: vs, e => .all v.name v.type (allList vs e)

end Effect

/-- A lifted action schema. -/
structure Action where
  name : Name
  params : List TypedVar
  pre : Formula
  eff : Effect
  deriving DecidableEq, Repr, Inhabited

/-- A PDDL domain. -/
structure Domain where
  name : Name
  /-- The requirement flags, e.g. `:typing`. -/
  requirements : List Name
  /-- The type hierarchy, as a list of `(type, direct supertype)` pairs.  The parser
  normalises the declaration so that every declared type reaches `object`. -/
  types : List (Name × Name)
  /-- The domain constants, with their declared types. -/
  constants : List TypedVar
  predicates : List PredicateDecl
  /-- Declared functions.  Only static functions (used for action costs) and the special
  0-ary function `total-cost` may occur. -/
  functions : List FunctionDecl
  actions : List Action
  deriving DecidableEq, Inhabited

/-- All type names occurring in a list of `(type, supertype)` edges. -/
def typeNames (es : List (Name × Name)) : List Name :=
  (es.flatMap (fun p => [p.1, p.2])).eraseDups

/-- Normalise a type hierarchy: every declared type that has no declared supertype becomes
a direct child of the built-in root type `object`. -/
def normalizeTypes (es : List (Name × Name)) : List (Name × Name) :=
  let names := typeNames es
  let missing := names.filter (fun t => t != "object" && !es.any (fun p => p.1 == t))
  es ++ missing.map (fun t => (t, "object"))

/-- An element of the initial state description of a problem. -/
inductive InitEl where
  /-- A ground atom `(p o₁ … oₙ)` that holds initially. -/
  | atom (p : Name) (args : List Name)
  /-- A static function value `(= (f o₁ … oₙ) v)`. -/
  | funAssign (f : Name) (args : List Name) (v : Int)
  deriving DecidableEq, Repr, Inhabited

/-- A PDDL problem. -/
structure Problem where
  name : Name
  /-- The name of the domain this problem belongs to. -/
  domain : Name
  requirements : List Name
  /-- The objects of the problem, with their declared types. -/
  objects : List TypedVar
  init : List InitEl
  goal : Formula
  /-- Whether the problem asks to minimise `(total-cost)`; other metrics are rejected by the
  parser. -/
  minimizeTotalCost : Bool
  deriving DecidableEq, Inhabited

/-- A ground atom: a predicate applied to object names.  States are sets of ground atoms. -/
structure Atom where
  pred : Name
  args : List Name
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace Atom

/-- Rendering a ground atom in concrete PDDL syntax. -/
def toString (a : Atom) : String :=
  "(" ++ String.intercalate " " (a.pred :: a.args) ++ ")"

instance : ToString Atom := ⟨toString⟩

end Atom

/-- A ground action, i.e. an action schema name together with the objects its parameters
are instantiated with. -/
structure GroundAction where
  name : Name
  args : List Name
  deriving DecidableEq, Repr, Inhabited

namespace GroundAction

/-- Rendering a ground action in IPC plan syntax. -/
def toString (a : GroundAction) : String :=
  "(" ++ String.intercalate " " (a.name :: a.args) ++ ")"

instance : ToString GroundAction := ⟨toString⟩

end GroundAction

end PDDL
