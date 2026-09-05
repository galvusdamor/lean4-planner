import Mathlib.Tactic
import pddl.Sexp

/-!
# The reader inverts the printer

`pddl.Sexp` provides the tokeniser and the s-expression reader of the PDDL front end, and
`Sexp.toString` prints an s-expression back into concrete syntax.  That the two fit together —
printing and reading gives back what one started with — has so far only been *tested*, by
running the front end over benchmark files.  This module *proves* it, at the level of
s-expressions:

* `PDDL.parseSexp_toString`: `parseSexp x.toString = .ok x`, and
* `PDDL.parseSexps_render`: the same for a whole sequence of s-expressions, written with any
  whitespace separator and followed by any amount of trailing whitespace (so a printed *file*
  is read back too).

Both need the obvious side condition that every atom of `x` is a name the tokeniser can
reproduce: nonempty, lower case, and free of whitespace, parentheses and `;` (`PDDL.AtomsOk`).
Without it there is nothing to prove — `(a b)` and `(a b)` written as one atom `a b` cannot be
told apart.

The proof follows the two stages of the front end: the character list of a printed
s-expression is tokenised to `PDDL.tokensOf x` (`PDDL.tokenizeAux_toString`), and the reader
turns those tokens back into `x` (`PDDL.readAux_tokensOf`).
-/

namespace PDDL

/-! ## Names the tokeniser reproduces -/

/-- A character that a name may contain: not whitespace, not a parenthesis, not `;`. -/
def okChar (c : Char) : Bool :=
  !Token.isWhitespace c && c != '(' && c != ')' && c != ';'

theorem okChar_iff {c : Char} : okChar c = true ↔
    (Token.isWhitespace c = false ∧ c ≠ '(' ∧ c ≠ ')' ∧ c ≠ ';') := by
  simp [okChar, and_assoc]

/-- A name that the tokeniser reproduces verbatim: nonempty, made of name characters, and
already lower case (the tokeniser folds case). -/
def okNameB (s : String) : Bool :=
  !s.isEmpty && s.toList.all okChar && s.toLower == s

theorem okNameB_iff {s : String} : okNameB s = true ↔
    (s ≠ "" ∧ (∀ c ∈ s.toList, okChar c) ∧ s.toLower = s) := by
  simp [okNameB, and_assoc]

/-- Every atom of the s-expression is a name the tokeniser reproduces. -/
inductive AtomsOk : Sexp → Prop
  /-- An atom is fine if its name is. -/
  | atom {s : String} : okNameB s = true → AtomsOk (.atom s)
  /-- A node is fine if all its children are. -/
  | node {xs : List Sexp} : (∀ x ∈ xs, AtomsOk x) → AtomsOk (.node xs)

/-! ## The tokens of an s-expression -/

/-- The tokens that a printed s-expression consists of. -/
def tokensOf : Sexp → List Token
  | .atom s => [Token.atom s]
  | .node xs => Token.lparen :: (xs.flatMap tokensOf) ++ [Token.rparen]

/-! ## Tokenising a printed s-expression -/

/-- The characters of a name are accumulated in the current token. -/
theorem tokenizeAux_atomChars :
    ∀ (cs : List Char) (cur : String) (rest : List Char) (acc : List Token),
      (∀ c ∈ cs, okChar c) →
      tokenizeAux (cs ++ rest) false cur acc
        = tokenizeAux rest false (cur ++ String.ofList cs) acc := by
  intro cs
  induction cs with
  | nil => intro cur rest acc _; simp
  | cons c cs ih =>
      intro cur rest acc h
      obtain ⟨h4, h2, h3, h1⟩ := okChar_iff.mp (h c (by simp))
      rw [List.cons_append, tokenizeAux]
      simp only [h1, h2, h3, h4, if_false, Bool.false_eq_true]
      rw [ih (cur.push c) rest acc (fun x hx => h x (by simp [hx]))]
      congr 1
      apply String.toList_inj.mp
      simp

/-- What may follow a printed s-expression: nothing, whitespace, or a closing parenthesis.
This is exactly the situation in which the name accumulated last is flushed into a token. -/
def RestOk (rest : List Char) : Prop :=
  rest = [] ∨ ∃ c t, rest = c :: t ∧ (Token.isWhitespace c = true ∨ c = ')')

/-- A name that is followed by a delimiter becomes an atom token. -/
theorem tokenizeAux_flushName (s : String) (rest : List Char) (acc : List Token)
    (hs : okNameB s = true) (hrest : RestOk rest) :
    tokenizeAux rest false s acc = tokenizeAux rest false "" (Token.atom s :: acc) := by
  obtain ⟨hne, -, hlow⟩ := okNameB_iff.mp hs
  have hflush : flush s acc = Token.atom s :: acc := by
    simp [flush, hne, hlow]
  rcases hrest with rfl | ⟨c, t, rfl, hc⟩
  · rw [tokenizeAux, tokenizeAux, hflush, flush]
    simp
  · rcases hc with hw | rfl
    · have h1 : c ≠ ';' := by intro h; rw [h] at hw; simp [Token.isWhitespace] at hw
      have h2 : c ≠ '(' := by intro h; rw [h] at hw; simp [Token.isWhitespace] at hw
      have h3 : c ≠ ')' := by intro h; rw [h] at hw; simp [Token.isWhitespace] at hw
      rw [tokenizeAux, tokenizeAux]
      simp only [h1, h2, h3, hw, if_false, if_true]
      rw [hflush, flush]
      simp
    · rw [tokenizeAux, tokenizeAux]
      norm_num [Token.isWhitespace]
      rw [hflush, flush]
      simp

/-! ### Printing a list of s-expressions -/

/-- A list of s-expressions, printed with the separator `w` between them. -/
def render (w : Char) (xs : List Sexp) : String :=
  String.intercalate (String.singleton w) (xs.map Sexp.toString)

/-- The characters of `render w xs`. -/
def renderChars (w : Char) : List Sexp → List Char
  | [] => []
  | [x] => x.toString.toList
  | x :: xs => x.toString.toList ++ w :: renderChars w xs

theorem toList_render (w : Char) (xs : List Sexp) :
    (render w xs).toList = renderChars w xs := by
  induction xs with
  | nil => simp [render, renderChars]
  | cons x xs ih =>
      cases xs with
      | nil => simp [render, renderChars]
      | cons y ys =>
          rw [show renderChars w (x :: y :: ys)
                = x.toString.toList ++ w :: renderChars w (y :: ys) from rfl]
          rw [render, String.toList_intercalate] at *
          simp only [List.map_cons] at *
          rw [List.intercalate, List.intersperse_cons_cons, List.flatten_cons, List.flatten_cons]
          rw [← ih]
          simp [List.intercalate]

/-- **Tokenising a printed s-expression** gives its tokens; the version for a list of
s-expressions separated by a whitespace character is proved simultaneously. -/
theorem tokenizeAux_toString : ∀ (x : Sexp) (rest : List Char) (acc : List Token),
    AtomsOk x → RestOk rest →
    tokenizeAux (x.toString.toList ++ rest) false "" acc
      = tokenizeAux rest false "" ((tokensOf x).reverse ++ acc) := by
  intro x
  induction x using Sexp.rec
    (motive_2 := fun xs => ∀ (w : Char) (rest : List Char) (acc : List Token),
      Token.isWhitespace w = true → (∀ y ∈ xs, AtomsOk y) → RestOk rest →
        tokenizeAux (renderChars w xs ++ rest) false "" acc
          = tokenizeAux rest false "" ((xs.flatMap tokensOf).reverse ++ acc)) with
  | atom s =>
      intro rest acc hok hrest
      have hs : okNameB s = true := by cases hok; assumption
      have hstr : (Sexp.atom s).toString = s := by simp [Sexp.toString]
      rw [hstr, tokenizeAux_atomChars s.toList "" rest acc
        (fun c hc => (okNameB_iff.mp hs).2.1 c hc)]
      have hcur : ("" : String) ++ String.ofList s.toList = s := by
        apply String.toList_inj.mp; simp
      rw [hcur, tokenizeAux_flushName s rest acc hs hrest]
      simp [tokensOf]
  | node xs ih =>
      intro rest acc hok hrest
      have hxs : ∀ y ∈ xs, AtomsOk y := by cases hok; assumption
      have hstr : (Sexp.node xs).toString.toList = '(' :: (renderChars ' ' xs ++ [')']) := by
        rw [show (Sexp.node xs).toString
          = "(" ++ String.intercalate " " (xs.map Sexp.toString) ++ ")" by simp [Sexp.toString]]
        rw [String.toList_append, String.toList_append,
          show String.intercalate " " (xs.map Sexp.toString) = render ' ' xs from rfl,
          toList_render]
        simp
      rw [hstr, List.cons_append, tokenizeAux]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
      norm_num [flush]
      rw [ih ' ' (')' :: rest) (Token.lparen :: acc) (by simp [Token.isWhitespace]) hxs
        (Or.inr ⟨')', rest, rfl, Or.inr rfl⟩)]
      rw [tokenizeAux]
      simp [flush, tokensOf]
  | nil =>
      rename_i w rest acc _ _ _
      simp [renderChars]
  | cons x xs ihx ihxs =>
      rename_i w rest acc hw hok hrest
      cases xs with
      | nil =>
          have hr : renderChars w [x] = x.toString.toList := rfl
          rw [hr, ihx rest acc (hok x (by simp)) hrest]
          simp
      | cons y ys =>
          have hr : renderChars w (x :: y :: ys)
              = x.toString.toList ++ w :: renderChars w (y :: ys) := rfl
          have h1 : w ≠ ';' := by intro h; rw [h] at hw; simp [Token.isWhitespace] at hw
          have h2 : w ≠ '(' := by intro h; rw [h] at hw; simp [Token.isWhitespace] at hw
          have h3 : w ≠ ')' := by intro h; rw [h] at hw; simp [Token.isWhitespace] at hw
          rw [hr, List.append_assoc, List.cons_append]
          rw [ihx (w :: (renderChars w (y :: ys) ++ rest)) acc (hok x (by simp))
            (Or.inr ⟨w, _, rfl, Or.inl hw⟩)]
          rw [tokenizeAux]
          simp only [h1, h2, h3, hw, if_false, if_true, flush, String.isEmpty_iff]
          rw [ihxs w rest ((tokensOf x).reverse ++ acc) hw (fun z hz => hok z (by simp [hz])) hrest]
          simp

/-- The list version of `tokenizeAux_toString`. -/
theorem tokenizeAux_renderChars (w : Char) (hw : Token.isWhitespace w = true) :
    ∀ (xs : List Sexp) (rest : List Char) (acc : List Token),
      (∀ y ∈ xs, AtomsOk y) → RestOk rest →
      tokenizeAux (renderChars w xs ++ rest) false "" acc
        = tokenizeAux rest false "" ((xs.flatMap tokensOf).reverse ++ acc) := by
  intro xs
  induction xs with
  | nil => intro rest acc _ _; simp [renderChars]
  | cons x xs ih =>
      intro rest acc hok hrest
      cases xs with
      | nil =>
          have hr : renderChars w [x] = x.toString.toList := rfl
          rw [hr, tokenizeAux_toString x rest acc (hok x (by simp)) hrest]
          simp
      | cons y ys =>
          have hr : renderChars w (x :: y :: ys)
              = x.toString.toList ++ w :: renderChars w (y :: ys) := rfl
          have h1 : w ≠ ';' := by intro h; rw [h] at hw; simp [Token.isWhitespace] at hw
          have h2 : w ≠ '(' := by intro h; rw [h] at hw; simp [Token.isWhitespace] at hw
          have h3 : w ≠ ')' := by intro h; rw [h] at hw; simp [Token.isWhitespace] at hw
          rw [hr, List.append_assoc, List.cons_append]
          rw [tokenizeAux_toString x (w :: (renderChars w (y :: ys) ++ rest)) acc
            (hok x (by simp)) (Or.inr ⟨w, _, rfl, Or.inl hw⟩)]
          rw [tokenizeAux]
          simp only [h1, h2, h3, hw, if_false, if_true, flush, String.isEmpty_iff]
          rw [ih rest ((tokensOf x).reverse ++ acc) (fun z hz => hok z (by simp [hz])) hrest]
          simp

/-- Trailing whitespace produces no tokens. -/
theorem tokenizeAux_whitespace : ∀ (cs : List Char) (acc : List Token),
    (∀ c ∈ cs, Token.isWhitespace c = true) → tokenizeAux cs false "" acc = acc.reverse := by
  intro cs
  induction cs with
  | nil => intro acc _; simp [tokenizeAux, flush]
  | cons c cs ih =>
      intro acc h
      have hw := h c (by simp)
      have h1 : c ≠ ';' := by intro hh; rw [hh] at hw; simp [Token.isWhitespace] at hw
      have h2 : c ≠ '(' := by intro hh; rw [hh] at hw; simp [Token.isWhitespace] at hw
      have h3 : c ≠ ')' := by intro hh; rw [hh] at hw; simp [Token.isWhitespace] at hw
      rw [tokenizeAux]
      simp only [h1, h2, h3, hw, if_false, if_true, flush, String.isEmpty_iff]
      exact ih acc (fun x hx => h x (by simp [hx]))

/-! ## Reading the tokens back -/

/-- **The reader turns the tokens of an s-expression back into it**; again the list version is
proved simultaneously. -/
theorem readAux_tokensOf : ∀ (x : Sexp) (ts : List Token) (cur : List Sexp)
    (st : List (List Sexp)),
    readAux (tokensOf x ++ ts) (cur :: st) = readAux ts ((x :: cur) :: st) := by
  intro x
  induction x using Sexp.rec
    (motive_2 := fun xs => ∀ (ts : List Token) (cur : List Sexp) (st : List (List Sexp)),
      readAux (xs.flatMap tokensOf ++ ts) (cur :: st)
        = readAux ts ((xs.reverse ++ cur) :: st)) with
  | atom s => intro ts cur st; rw [tokensOf]; simp [readAux]
  | node xs ih =>
      intro ts cur st
      rw [tokensOf]
      simp only [List.cons_append, List.append_assoc, List.nil_append]
      rw [readAux, ih (Token.rparen :: ts) [] (cur :: st), readAux]
      simp
  | nil => rename_i ts cur st; simp
  | cons x xs ihx ihxs =>
      rename_i ts cur st
      rw [List.flatMap_cons, List.append_assoc, ihx (xs.flatMap tokensOf ++ ts) cur st,
        ihxs ts (x :: cur) st]
      simp

/-- Reading the tokens of a list of s-expressions gives that list. -/
theorem readSexps_flatMap (xs : List Sexp) : readSexps (xs.flatMap tokensOf) = .ok xs := by
  have h : ∀ (xs : List Sexp) (ts : List Token) (cur : List Sexp) (st : List (List Sexp)),
      readAux (xs.flatMap tokensOf ++ ts) (cur :: st)
        = readAux ts ((xs.reverse ++ cur) :: st) := by
    intro xs
    induction xs with
    | nil => intro ts cur st; simp
    | cons x xs ih =>
        intro ts cur st
        rw [List.flatMap_cons, List.append_assoc, readAux_tokensOf x _ cur st, ih ts (x :: cur) st]
        simp
  rw [readSexps, show xs.flatMap tokensOf = xs.flatMap tokensOf ++ [] by simp, h xs [] [] []]
  simp [readAux]

/-! ## The round trip -/

/-- **Reading a printed sequence of s-expressions gives it back.**  The s-expressions are
separated by the whitespace character `w` and may be followed by any amount of whitespace, so
this covers a printed file. -/
theorem parseSexps_render (w : Char) (hw : Token.isWhitespace w = true) (xs : List Sexp)
    (hok : ∀ x ∈ xs, AtomsOk x) (tail : String)
    (htail : ∀ c ∈ tail.toList, Token.isWhitespace c = true) :
    parseSexps (render w xs ++ tail) = .ok xs := by
  have hrest : RestOk tail.toList := by
    cases h : tail.toList with
    | nil => exact Or.inl rfl
    | cons c t => exact Or.inr ⟨c, t, rfl, Or.inl (htail c (by rw [h]; simp))⟩
  have htok : tokenize (render w xs ++ tail) = xs.flatMap tokensOf := by
    rw [tokenize, String.toList_append, toList_render,
      tokenizeAux_renderChars w hw xs tail.toList [] hok hrest,
      tokenizeAux_whitespace tail.toList _ htail]
    simp
  rw [parseSexps, htok, readSexps_flatMap]

/-- **Reading a printed s-expression gives it back.** -/
theorem parseSexp_toString (x : Sexp) (hok : AtomsOk x) : parseSexp x.toString = .ok x := by
  have hrender : render ' ' [x] = x.toString := by
    apply String.toList_inj.mp
    rw [toList_render]
    rfl
  have h : parseSexps x.toString = .ok [x] := by
    have := parseSexps_render ' ' (by simp [Token.isWhitespace]) [x]
      (by intro y hy; rw [List.mem_singleton.mp hy]; exact hok) "" (by simp)
    rwa [hrender, show x.toString ++ "" = x.toString by simp] at this
  rw [parseSexp, h]
  rfl

end PDDL
