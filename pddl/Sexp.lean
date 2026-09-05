/-!
# S-expressions for PDDL

PDDL files are written in a LISP-like syntax.  This module provides the lowest layer of the
PDDL front end: a tokeniser and a reader turning the token stream into s-expressions.

The reader is deliberately independent of PDDL itself; all PDDL specific knowledge lives in
`pddl.Parser`.

Two conventions are implemented here, both mandated by the PDDL definition:

* everything from a `;` up to (and including) the end of the line is a comment, and
* PDDL is case insensitive, so every token is folded to lower case.
-/

namespace PDDL

/-- A PDDL token: an opening parenthesis, a closing parenthesis or a name-like token. -/
inductive Token where
  | lparen
  | rparen
  | atom (s : String)
  deriving DecidableEq, Repr, Inhabited

namespace Token

/-- Characters that separate tokens. -/
def isWhitespace (c : Char) : Bool :=
  c = ' ' || c = '\t' || c = '\n' || c = '\r' || c = '\u000c'

end Token

/-- Push the token accumulated in `cur` (if any) onto the reversed token list `acc`. -/
private def flush (cur : String) (acc : List Token) : List Token :=
  if cur.isEmpty then acc else Token.atom cur.toLower :: acc

/-- Tokeniser worker.  `inComment` records whether we are inside a `;` comment, `cur`
is the name token read so far and `acc` the (reversed) list of tokens produced so far. -/
private def tokenizeAux : List Char → Bool → String → List Token → List Token
  | [], _, cur, acc => (flush cur acc).reverse
  | c :: cs, true, cur, acc =>
      tokenizeAux cs (c != '\n') cur acc
  | c :: cs, false, cur, acc =>
      if c = ';' then
        tokenizeAux cs true "" (flush cur acc)
      else if c = '(' then
        tokenizeAux cs false "" (Token.lparen :: flush cur acc)
      else if c = ')' then
        tokenizeAux cs false "" (Token.rparen :: flush cur acc)
      else if Token.isWhitespace c then
        tokenizeAux cs false "" (flush cur acc)
      else
        tokenizeAux cs false (cur.push c) acc

/-- Split a PDDL source text into tokens, dropping comments and folding case. -/
def tokenize (s : String) : List Token :=
  tokenizeAux s.toList false "" []

/-- An s-expression: either a name-like atom or a parenthesised list. -/
inductive Sexp where
  | atom (s : String)
  | node (xs : List Sexp)
  deriving Inhabited

namespace Sexp

/-- Render an s-expression back into concrete syntax (used for error messages). -/
partial def toString : Sexp → String
  | .atom s => s
  | .node xs => "(" ++ String.intercalate " " (xs.map toString) ++ ")"

instance : ToString Sexp := ⟨toString⟩

end Sexp

/-- Reader worker.  `stack` holds the (reversed) lists of the s-expressions that are
currently open, innermost first. -/
private def readAux : List Token → List (List Sexp) → Except String (List Sexp)
  | [], [top] => .ok top.reverse
  | [], _ => .error "unexpected end of input: missing ')'"
  | Token.lparen :: ts, stack => readAux ts ([] :: stack)
  | Token.rparen :: ts, cur :: parent :: rest =>
      readAux ts ((Sexp.node cur.reverse :: parent) :: rest)
  | Token.rparen :: _, _ => .error "unexpected ')'"
  | Token.atom s :: ts, cur :: rest => readAux ts ((Sexp.atom s :: cur) :: rest)
  | Token.atom _ :: _, [] => .error "internal error: empty s-expression stack"

/-- Read a sequence of s-expressions from a token list. -/
def readSexps (ts : List Token) : Except String (List Sexp) :=
  readAux ts [[]]

/-- Read a PDDL source text as a sequence of s-expressions. -/
def parseSexps (s : String) : Except String (List Sexp) :=
  readSexps (tokenize s)

/-- Read a PDDL source text that must contain exactly one s-expression. -/
def parseSexp (s : String) : Except String Sexp := do
  match ← parseSexps s with
  | [x] => .ok x
  | [] => .error "empty input"
  | _ => .error "expected exactly one top-level s-expression"

end PDDL
