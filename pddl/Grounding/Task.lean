import pddl.Semantics

/-!
# An intermediate grounded representation

This module defines `PDDL.GroundTask`, the target of the grounder defined in
`pddl.Grounding.Compile`.  A ground task is a purely propositional planning task whose
propositions are the ground atoms of the PDDL instance it came from; no variables, types
or quantifiers occur any more.

The representation is deliberately more general than `STRIPS.PlanningTask`, so that the
whole supported (ADL) fragment can be grounded without changing its semantics:

* conditions (operator preconditions, effect conditions and the goal) are conjunctions of
  *literals* (`Lit`), so negative conditions are expressible under the closed world
  assumption;
* the goal is a *disjunction* of such conjunctions (`GroundTask.goal : List (List Lit)`),
  which is what a disjunctive goal compiles to; a task whose goal is a single clause is the
  usual conjunctive case, and the empty disjunction is the unsatisfiable goal;
* an operator carries a list of *conditional* effects (`CondEff`), an unconditional
  operator being one all of whose effect conditions are empty (`GroundOp.Unconditional`);
* operators remember the lifted ground action (`GroundOp.action`) they were produced from,
  so that a plan for the ground task can be read back as a plan for the PDDL instance.
  Note that one ground action may give rise to *several* operators, namely one per disjunct
  of its precondition.

The translation to `STRIPS.PlanningTask` in `pddl.Grounding.Strips` is only defined for
tasks that are unconditional, positive and have a single goal clause; the compilations
removing conditional effects and negative literals are separate, verified steps
(`pddl.Grounding.Positive`).

Since the propositions of a ground task *are* the ground atoms of the instance, states of
the ground task are literally states of the PDDL instance (`PDDL.State = Set Atom`); this
keeps the correctness statement in `pddl.Grounding.Correct` free of any state translation.
-/

namespace PDDL

/-! ### Removing duplicate atoms -/

instance : LawfulHashable Atom where
  hash_eq a b h := by
    have : a = b := eq_of_beq h
    subst this
    rfl

/-- Auxiliary function of `dedupAtoms`: keep the atoms of the list that have not been seen
yet. -/
def dedupAtomsAux : List Atom → Std.HashSet Atom → List Atom
  | [], _ => []
  | a :: as, seen =>
      if seen.contains a then dedupAtomsAux as seen
      else a :: dedupAtomsAux as (seen.insert a)

theorem mem_dedupAtomsAux (l : List Atom) (seen : Std.HashSet Atom) (a : Atom) :
    a ∈ dedupAtomsAux l seen ↔ a ∈ l ∧ a ∉ seen := by
  induction l generalizing seen with
  | nil => simp [dedupAtomsAux]
  | cons b bs ih =>
    by_cases hb : seen.contains b
    · have hb' : b ∈ seen := Std.HashSet.mem_iff_contains.2 hb
      simp only [dedupAtomsAux, if_pos hb, ih, List.mem_cons]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨Or.inr h1, h2⟩
      · rintro ⟨(rfl | h1), h2⟩
        · exact absurd hb' h2
        · exact ⟨h1, h2⟩
    · have hb' : b ∉ seen := fun h => hb (Std.HashSet.mem_iff_contains.1 h)
      simp only [dedupAtomsAux, if_neg hb, List.mem_cons, ih, Std.HashSet.mem_insert,
        beq_iff_eq, not_or]
      constructor
      · rintro (rfl | ⟨h1, -, h3⟩)
        · exact ⟨Or.inl rfl, hb'⟩
        · exact ⟨Or.inr h1, h3⟩
      · rintro ⟨(rfl | h1), h2⟩
        · exact Or.inl rfl
        · by_cases hab : a = b
          · exact Or.inl hab
          · exact Or.inr ⟨h1, fun h => hab h.symm, h2⟩

theorem nodup_dedupAtomsAux (l : List Atom) (seen : Std.HashSet Atom) :
    (dedupAtomsAux l seen).Nodup := by
  induction l generalizing seen with
  | nil => simp [dedupAtomsAux]
  | cons b bs ih =>
    by_cases hb : seen.contains b
    · rw [dedupAtomsAux, if_pos hb]
      exact ih seen
    · rw [dedupAtomsAux, if_neg hb]
      refine List.nodup_cons.2 ⟨fun h => ?_, ih _⟩
      have hmem := (mem_dedupAtomsAux bs (seen.insert b) b).1 h
      exact hmem.2 (Std.HashSet.mem_insert.2 (Or.inl (by simp)))

/-- Remove duplicates from a list of atoms.  Unlike `List.dedup` this uses a hash set and
is therefore linear rather than quadratic, which matters because full grounding produces
very long atom lists. -/
def dedupAtoms (l : List Atom) : List Atom := dedupAtomsAux l ∅

@[simp] theorem mem_dedupAtoms {l : List Atom} {a : Atom} : a ∈ dedupAtoms l ↔ a ∈ l := by
  simp [dedupAtoms, mem_dedupAtomsAux]

theorem nodup_dedupAtoms (l : List Atom) : (dedupAtoms l).Nodup := nodup_dedupAtomsAux l ∅

/-! ### Literals -/

/-- A ground literal: an atom or a negated atom.  Under the closed world assumption a
negative literal `neg a` holds in a state exactly when `a` is not an element of it. -/
inductive Lit where
  /-- The positive literal `a`. -/
  | pos (a : Atom)
  /-- The negative literal `¬ a`. -/
  | neg (a : Atom)
  deriving DecidableEq, Repr, Inhabited

namespace Lit

/-- The atom underlying a literal. -/
def atom : Lit → Atom
  | .pos a => a
  | .neg a => a

@[simp] theorem atom_pos (a : Atom) : (Lit.pos a).atom = a := rfl
@[simp] theorem atom_neg (a : Atom) : (Lit.neg a).atom = a := rfl

/-- The literal holds in the state `s`. -/
def Holds : Lit → State → Prop
  | .pos a, s => a ∈ s
  | .neg a, s => a ∉ s

@[simp] theorem holds_pos {a : Atom} {s : State} : (Lit.pos a).Holds s ↔ a ∈ s := Iff.rfl
@[simp] theorem holds_neg {a : Atom} {s : State} : (Lit.neg a).Holds s ↔ a ∉ s := Iff.rfl

/-- The complement of a literal. -/
def complement : Lit → Lit
  | .pos a => .neg a
  | .neg a => .pos a

@[simp] theorem holds_complement {l : Lit} {s : State} :
    l.complement.Holds s ↔ ¬ l.Holds s := by
  cases l <;> simp [complement]

/-- The literal is positive. -/
def IsPos : Lit → Prop
  | .pos _ => True
  | .neg _ => False

/-- Executable test for positivity. -/
def isPosB : Lit → Bool
  | .pos _ => true
  | .neg _ => false

@[simp] theorem isPosB_iff {l : Lit} : l.isPosB = true ↔ l.IsPos := by
  cases l <;> simp [isPosB, IsPos]

theorem holds_of_isPos {l : Lit} (h : l.IsPos) {s : State} : l.Holds s ↔ l.atom ∈ s := by
  cases l with
  | pos a => simp
  | neg a => exact absurd h (by simp [IsPos])

end Lit

/-- A conjunction of literals (a *clause* of the disjunctive normal form used by the
grounder) holds in the state `s`. -/
def ClauseHolds (c : List Lit) (s : State) : Prop := ∀ l ∈ c, l.Holds s

@[simp] theorem clauseHolds_nil (s : State) : ClauseHolds [] s := by
  intro l hl; cases hl

@[simp] theorem clauseHolds_cons {l : Lit} {c : List Lit} {s : State} :
    ClauseHolds (l :: c) s ↔ l.Holds s ∧ ClauseHolds c s := by
  simp only [ClauseHolds, List.mem_cons, forall_eq_or_imp]

@[simp] theorem clauseHolds_append {c₁ c₂ : List Lit} {s : State} :
    ClauseHolds (c₁ ++ c₂) s ↔ ClauseHolds c₁ s ∧ ClauseHolds c₂ s := by
  simp only [ClauseHolds, List.mem_append]
  constructor
  · exact fun h => ⟨fun l hl => h l (Or.inl hl), fun l hl => h l (Or.inr hl)⟩
  · rintro ⟨h₁, h₂⟩ l (hl | hl)
    · exact h₁ l hl
    · exact h₂ l hl

/-- A clause of positive literals holds exactly when all its atoms are in the state. -/
theorem clauseHolds_of_pos {c : List Lit} (h : ∀ l ∈ c, l.IsPos) (s : State) :
    ClauseHolds c s ↔ ∀ a ∈ c.map Lit.atom, a ∈ s := by
  simp only [ClauseHolds, List.mem_map]
  constructor
  · rintro hc a ⟨l, hl, rfl⟩
    exact (Lit.holds_of_isPos (h l hl)).1 (hc l hl)
  · intro ha l hl
    exact (Lit.holds_of_isPos (h l hl)).2 (ha _ ⟨l, hl, rfl⟩)

/-- A *disjunctive normal form*: a disjunction of conjunctions of literals. -/
abbrev Dnf := List (List Lit)

/-- A DNF holds in a state if one of its clauses does. -/
def DnfHolds (d : Dnf) (s : State) : Prop := ∃ c ∈ d, ClauseHolds c s

@[simp] theorem dnfHolds_nil (s : State) : ¬ DnfHolds [] s := by simp [DnfHolds]

@[simp] theorem dnfHolds_cons {c : List Lit} {d : Dnf} {s : State} :
    DnfHolds (c :: d) s ↔ ClauseHolds c s ∨ DnfHolds d s := by
  simp only [DnfHolds, List.mem_cons, exists_eq_or_imp]

@[simp] theorem dnfHolds_append {d₁ d₂ : Dnf} {s : State} :
    DnfHolds (d₁ ++ d₂) s ↔ DnfHolds d₁ s ∨ DnfHolds d₂ s := by
  simp only [DnfHolds, List.mem_append]
  constructor
  · rintro ⟨c, hc | hc, h⟩
    · exact Or.inl ⟨c, hc, h⟩
    · exact Or.inr ⟨c, hc, h⟩
  · rintro (⟨c, hc, h⟩ | ⟨c, hc, h⟩)
    · exact ⟨c, Or.inl hc, h⟩
    · exact ⟨c, Or.inr hc, h⟩

/-! ### Operators -/

/-- A single conditional effect of a ground operator: if all literals of `cond` hold in
the current state, the atoms of `add` are made true and those of `del` are made false.  An
unconditional effect is one with `cond = []`. -/
structure CondEff where
  cond : List Lit
  add : List Atom
  del : List Atom
  deriving DecidableEq, Repr, Inhabited

namespace CondEff

/-- The condition of the conditional effect holds in the state `s`. -/
def Triggered (ce : CondEff) (s : State) : Prop := ClauseHolds ce.cond s

theorem triggered_nil {ce : CondEff} (h : ce.cond = []) (s : State) : ce.Triggered s := by
  simp [Triggered, h]

end CondEff

/-- A ground operator: a precondition (a conjunction of literals), a list of conditional
effects and a cost, together with the ground action of the original PDDL instance it was
produced from. -/
structure GroundOp where
  /-- The ground action of the lifted instance this operator was produced from. -/
  action : GroundAction
  /-- The precondition: the conjunction of these literals. -/
  pre : List Lit
  /-- The (conditional) effects. -/
  effs : List CondEff
  /-- The cost of the operator. -/
  cost : Int
  deriving DecidableEq, Repr, Inhabited

namespace GroundOp

/-- The operator is applicable in the state `s`. -/
def Applicable (op : GroundOp) (s : State) : Prop := ClauseHolds op.pre s

/-- The set of atoms added by the operator in the state `s`. -/
def addSet (op : GroundOp) (s : State) : Set Atom :=
  {a | ∃ ce ∈ op.effs, ce.Triggered s ∧ a ∈ ce.add}

/-- The set of atoms deleted by the operator in the state `s`. -/
def delSet (op : GroundOp) (s : State) : Set Atom :=
  {a | ∃ ce ∈ op.effs, ce.Triggered s ∧ a ∈ ce.del}

/-- The successor state: delete first, then add (so adds win over deletes). -/
def result (op : GroundOp) (s : State) : State := (s \ op.delSet s) ∪ op.addSet s

theorem mem_result {op : GroundOp} {s : State} {a : Atom} :
    a ∈ op.result s ↔ a ∈ op.addSet s ∨ (a ∈ s ∧ a ∉ op.delSet s) := by
  simp [result, or_comm]

/-- The operator has no conditional effects. -/
def Unconditional (op : GroundOp) : Prop := ∀ ce ∈ op.effs, ce.cond = []

/-- The operator has no negative literals in its precondition or effect conditions. -/
def Positive (op : GroundOp) : Prop :=
  (∀ l ∈ op.pre, l.IsPos) ∧ ∀ ce ∈ op.effs, ∀ l ∈ ce.cond, l.IsPos

/-- The atoms of the precondition (relevant for positive operators). -/
def preAtoms (op : GroundOp) : List Atom := op.pre.map Lit.atom

theorem applicable_of_positive {op : GroundOp} (h : op.Positive) (s : State) :
    op.Applicable s ↔ ∀ a ∈ op.preAtoms, a ∈ s :=
  clauseHolds_of_pos h.1 s

/-- All atoms added by the operator (relevant for unconditional operators). -/
def addList (op : GroundOp) : List Atom := op.effs.flatMap (·.add)

/-- All atoms deleted by the operator (relevant for unconditional operators). -/
def delList (op : GroundOp) : List Atom := op.effs.flatMap (·.del)

theorem mem_addList_of_mem_addSet {op : GroundOp} {s : State} {a : Atom}
    (h : a ∈ op.addSet s) : a ∈ op.addList := by
  obtain ⟨ce, hce, -, ha⟩ := h
  exact List.mem_flatMap.2 ⟨ce, hce, ha⟩

theorem addSet_of_unconditional {op : GroundOp} (h : op.Unconditional) (s : State) :
    op.addSet s = {a | a ∈ op.addList} := by
  ext a
  simp only [addSet, addList, Set.mem_setOf_eq, List.mem_flatMap]
  constructor
  · rintro ⟨ce, hce, -, ha⟩; exact ⟨ce, hce, ha⟩
  · rintro ⟨ce, hce, ha⟩; exact ⟨ce, hce, CondEff.triggered_nil (h ce hce) s, ha⟩

theorem delSet_of_unconditional {op : GroundOp} (h : op.Unconditional) (s : State) :
    op.delSet s = {a | a ∈ op.delList} := by
  ext a
  simp only [delSet, delList, Set.mem_setOf_eq, List.mem_flatMap]
  constructor
  · rintro ⟨ce, hce, -, ha⟩; exact ⟨ce, hce, ha⟩
  · rintro ⟨ce, hce, ha⟩; exact ⟨ce, hce, CondEff.triggered_nil (h ce hce) s, ha⟩

/-- Executable check that an operator has no conditional effects. -/
def unconditionalB (op : GroundOp) : Bool := op.effs.all (fun ce => ce.cond.isEmpty)

theorem unconditionalB_iff {op : GroundOp} : op.unconditionalB = true ↔ op.Unconditional := by
  simp only [unconditionalB, List.all_eq_true, List.isEmpty_iff, Unconditional]

/-- Executable check that an operator has no negative literals. -/
def positiveB (op : GroundOp) : Bool :=
  op.pre.all Lit.isPosB && op.effs.all (fun ce => ce.cond.all Lit.isPosB)

theorem positiveB_iff {op : GroundOp} : op.positiveB = true ↔ op.Positive := by
  simp only [positiveB, Bool.and_eq_true, List.all_eq_true, Lit.isPosB_iff, Positive]

/-- All atoms mentioned by an operator. -/
def atomList (op : GroundOp) : List Atom :=
  op.preAtoms ++ op.effs.flatMap (fun ce => ce.cond.map Lit.atom ++ ce.add ++ ce.del)

theorem mem_atomList_of_mem_pre {op : GroundOp} {l : Lit} (h : l ∈ op.pre) :
    l.atom ∈ op.atomList := by
  simp only [atomList, preAtoms, List.mem_append, List.mem_map]
  exact Or.inl ⟨l, h, rfl⟩

theorem mem_atomList_of_mem_preAtoms {op : GroundOp} {a : Atom} (h : a ∈ op.preAtoms) :
    a ∈ op.atomList := by simp [atomList, h]

theorem mem_atomList_of_mem_add {op : GroundOp} {ce : CondEff} {a : Atom}
    (hce : ce ∈ op.effs) (h : a ∈ ce.add) : a ∈ op.atomList := by
  simp only [atomList, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨ce, hce, by simp [h]⟩

theorem mem_atomList_of_mem_del {op : GroundOp} {ce : CondEff} {a : Atom}
    (hce : ce ∈ op.effs) (h : a ∈ ce.del) : a ∈ op.atomList := by
  simp only [atomList, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨ce, hce, by simp [h]⟩

theorem mem_atomList_of_mem_cond {op : GroundOp} {ce : CondEff} {l : Lit}
    (hce : ce ∈ op.effs) (h : l ∈ ce.cond) : l.atom ∈ op.atomList := by
  simp only [atomList, List.mem_append, List.mem_flatMap]
  refine Or.inr ⟨ce, hce, ?_⟩
  simp only [List.mem_map]
  exact Or.inl (Or.inl ⟨l, h, rfl⟩)

theorem mem_atomList_of_mem_addList {op : GroundOp} {a : Atom} (h : a ∈ op.addList) :
    a ∈ op.atomList := by
  obtain ⟨ce, hce, ha⟩ := List.mem_flatMap.1 h
  exact mem_atomList_of_mem_add hce ha

theorem mem_atomList_of_mem_delList {op : GroundOp} {a : Atom} (h : a ∈ op.delList) :
    a ∈ op.atomList := by
  obtain ⟨ce, hce, ha⟩ := List.mem_flatMap.1 h
  exact mem_atomList_of_mem_del hce ha

end GroundOp

/-- A ground planning task: a list of operators, an initial state given as a list of atoms
and a goal given in disjunctive normal form. -/
structure GroundTask where
  ops : List GroundOp
  init : List Atom
  goal : Dnf
  deriving DecidableEq, Repr, Inhabited

namespace GroundTask

/-- The initial state of a ground task. -/
def initState (T : GroundTask) : State := {a | a ∈ T.init}

/-- The goal holds in the state `s`. -/
def GoalHolds (T : GroundTask) (s : State) : Prop := DnfHolds T.goal s

/-- Executing a sequence of operators of the task. -/
inductive Execution (T : GroundTask) : State → List GroundOp → State → Prop
  | nil (s : State) : Execution T s [] s
  | cons {s s' : State} {op : GroundOp} {π : List GroundOp} :
      op ∈ T.ops → op.Applicable s → Execution T (op.result s) π s' →
      Execution T s (op :: π) s'

theorem Execution.mem_ops {T : GroundTask} {s s' : State} {π : List GroundOp}
    (h : T.Execution s π s') : ∀ op ∈ π, op ∈ T.ops := by
  induction h with
  | nil => simp
  | cons hop _ _ ih =>
    intro o ho
    rcases List.mem_cons.1 ho with rfl | ho
    · exact hop
    · exact ih _ ho

theorem Execution.unique {T : GroundTask} {s s₁ s₂ : State} {π : List GroundOp}
    (h₁ : T.Execution s π s₁) (h₂ : T.Execution s π s₂) : s₁ = s₂ := by
  induction h₁ with
  | nil s => cases h₂; rfl
  | cons _ _ _ ih => cases h₂ with | cons _ _ h => exact ih h

theorem Execution.append {T : GroundTask} {s₁ s₂ s₃ : State} {π₁ π₂ : List GroundOp}
    (h₁ : T.Execution s₁ π₁ s₂) (h₂ : T.Execution s₂ π₂ s₃) :
    T.Execution s₁ (π₁ ++ π₂) s₃ := by
  induction h₁ with
  | nil => simpa using h₂
  | cons hop happ _ ih => exact Execution.cons hop happ (ih h₂)

/-- `π` is a plan for the ground task. -/
def IsPlan (T : GroundTask) (π : List GroundOp) : Prop :=
  ∃ s, T.Execution T.initState π s ∧ T.GoalHolds s

/-- The cost of a sequence of operators. -/
def planCost (π : List GroundOp) : Int := (π.map (·.cost)).sum

/-- Solvability of a ground task. -/
def Solvable (T : GroundTask) : Prop := ∃ π, T.IsPlan π

/-- All atoms occurring in a ground task; these are the propositional variables of the
task. -/
def atoms (T : GroundTask) : List Atom :=
  dedupAtoms (T.init ++ T.goal.flatMap (fun c => c.map Lit.atom) ++
    T.ops.flatMap GroundOp.atomList)

theorem atoms_nodup (T : GroundTask) : T.atoms.Nodup := nodup_dedupAtoms _

theorem mem_atoms {T : GroundTask} {a : Atom} :
    a ∈ T.atoms ↔ a ∈ T.init ∨ (∃ c ∈ T.goal, a ∈ c.map Lit.atom) ∨
      ∃ op ∈ T.ops, a ∈ op.atomList := by
  simp only [atoms, mem_dedupAtoms, List.mem_append, List.mem_flatMap, or_assoc]

theorem mem_atoms_of_mem_init {T : GroundTask} {a : Atom} (h : a ∈ T.init) : a ∈ T.atoms :=
  mem_atoms.2 (Or.inl h)

theorem mem_atoms_of_mem_goal {T : GroundTask} {c : List Lit} {l : Lit} (hc : c ∈ T.goal)
    (h : l ∈ c) : l.atom ∈ T.atoms :=
  mem_atoms.2 (Or.inr (Or.inl ⟨c, hc, List.mem_map_of_mem h⟩))

theorem mem_atoms_of_mem_op {T : GroundTask} {op : GroundOp} {a : Atom} (hop : op ∈ T.ops)
    (h : a ∈ op.atomList) : a ∈ T.atoms :=
  mem_atoms.2 (Or.inr (Or.inr ⟨op, hop, h⟩))

/-- A ground task is unconditional if all its operators are. -/
def Unconditional (T : GroundTask) : Prop := ∀ op ∈ T.ops, op.Unconditional

/-- Executable check that a ground task has no conditional effects. -/
def unconditionalB (T : GroundTask) : Bool := T.ops.all GroundOp.unconditionalB

theorem unconditionalB_iff {T : GroundTask} : T.unconditionalB = true ↔ T.Unconditional := by
  simp only [unconditionalB, List.all_eq_true, Unconditional,
    GroundOp.unconditionalB_iff]

/-- A ground task is positive if no negative literal occurs in an operator or in the
goal. -/
def Positive (T : GroundTask) : Prop :=
  (∀ op ∈ T.ops, op.Positive) ∧ ∀ c ∈ T.goal, ∀ l ∈ c, l.IsPos

/-- Executable check that a ground task contains no negative literals. -/
def positiveB (T : GroundTask) : Bool :=
  T.ops.all GroundOp.positiveB && T.goal.all (fun c => c.all Lit.isPosB)

theorem positiveB_iff {T : GroundTask} : T.positiveB = true ↔ T.Positive := by
  simp only [positiveB, Bool.and_eq_true, List.all_eq_true, GroundOp.positiveB_iff,
    Lit.isPosB_iff, Positive]

/-- The task has a conjunctive (non-disjunctive) goal. -/
def ConjunctiveGoal (T : GroundTask) : Prop := ∃ c, T.goal = [c]

/-- Executable check for a conjunctive goal. -/
def conjunctiveGoalB (T : GroundTask) : Bool := T.goal.length == 1

theorem conjunctiveGoalB_iff {T : GroundTask} :
    T.conjunctiveGoalB = true ↔ T.ConjunctiveGoal := by
  simp only [conjunctiveGoalB, beq_iff_eq, ConjunctiveGoal, List.length_eq_one_iff]

/-- The atoms of the goal clause of a task with a conjunctive goal. -/
def goalAtoms (T : GroundTask) : List Atom := (T.goal.flatMap id).map Lit.atom

theorem mem_atoms_of_mem_goalAtoms {T : GroundTask} {a : Atom} (h : a ∈ T.goalAtoms) :
    a ∈ T.atoms := by
  simp only [goalAtoms, List.mem_map, List.mem_flatMap, id_eq] at h
  obtain ⟨l, ⟨c, hc, hl⟩, rfl⟩ := h
  exact mem_atoms_of_mem_goal hc hl

theorem goalHolds_of_conjunctive_positive {T : GroundTask} (hc : T.ConjunctiveGoal)
    (hp : ∀ c ∈ T.goal, ∀ l ∈ c, l.IsPos) (s : State) :
    T.GoalHolds s ↔ ∀ a ∈ T.goalAtoms, a ∈ s := by
  obtain ⟨c, hgoal⟩ := hc
  have hpos : ∀ l ∈ c, l.IsPos := hp c (by simp [hgoal])
  simp only [GoalHolds, goalAtoms, hgoal, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, id_eq, DnfHolds, List.mem_singleton, exists_eq_left]
  exact clauseHolds_of_pos hpos s

/-- The ground tasks that can be translated to `STRIPS.PlanningTask`: no conditional
effects, no negative literals and a single (conjunctive) goal clause. -/
structure StripsReady (T : GroundTask) : Prop where
  unconditional : T.Unconditional
  positive : T.Positive
  conjGoal : T.ConjunctiveGoal

/-- Executable check for `GroundTask.StripsReady`. -/
def stripsReadyB (T : GroundTask) : Bool :=
  T.unconditionalB && T.positiveB && T.conjunctiveGoalB

theorem stripsReadyB_iff {T : GroundTask} : T.stripsReadyB = true ↔ T.StripsReady := by
  simp only [stripsReadyB, Bool.and_eq_true, unconditionalB_iff, positiveB_iff,
    conjunctiveGoalB_iff]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, h₃⟩; exact ⟨h₁, h₂, h₃⟩
  · rintro ⟨h₁, h₂, h₃⟩; exact ⟨⟨h₁, h₂⟩, h₃⟩

end GroundTask

end PDDL
