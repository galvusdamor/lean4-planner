import pddl.Grounding.Strips

/-!
# Positive normal form of a ground task

A `GroundTask` produced by the grounder may contain negative literals in preconditions,
effect conditions and the goal, because PDDL allows negative preconditions and the closed
world assumption gives them a meaning.  STRIPS operators, on the other hand, have purely
positive preconditions.  This module implements the standard *positive normal form*
compilation and proves that it preserves the semantics.

For every atom `a` a complementary atom `encAtom a` is introduced, which is intended to be
true exactly when `a` is false.  It is written with the reserved predicate name `"¬"` and
the predicate name of `a` as its first argument, so that the encoding is injective and
cannot clash with a predicate of the original task (a condition that is checked by
`GroundTask.negFreshB`, and which holds for every task coming from a parsed PDDL file).
Every negative literal `¬ a` is replaced by the positive literal `encAtom a`, and every
operator maintains the complementary atoms: what it adds it deletes in complemented form
and vice versa.

The compilation is defined for tasks *without conditional effects*
(`GroundTask.Unconditional`); with conditional effects the invariant `encAtom a` ↔ `¬ a`
cannot be maintained by a conjunction of conditional effects with conjunctive conditions,
because whether an atom survives depends on which other effects trigger.

The main results are, for an unconditional task `T` with `T.NegFresh`:

* `GroundTask.toPositive_positive`, `GroundTask.toPositive_unconditional`: the compiled
  task is positive and unconditional (and `GroundTask.toPositive_stripsReady` if the goal
  of `T` is conjunctive);
* `GroundTask.encState_result`, `GroundTask.applicable_encOp_iff`: applicability and the
  successor state agree under the state encoding `GroundTask.encState`;
* `GroundTask.toPositive_isPlan_iff`, `GroundTask.toPositive_planCost` and
  `GroundTask.toPositive_solvable_iff`: the plans of the compiled task are exactly the
  plans of `T` (operator by operator, and hence with the same underlying ground actions and
  the same cost).
-/

namespace PDDL

namespace GroundTask

/-! ### The complementary atoms -/

/-- The atom expressing that `a` is false.  It uses the reserved predicate name `"¬"`,
which no atom of a parsed PDDL instance can have, and keeps the predicate name of `a` as
its first argument, which makes the encoding injective. -/
def encAtom (a : Atom) : Atom := ⟨"¬", a.pred :: a.args⟩

@[simp] theorem encAtom_pred (a : Atom) : (encAtom a).pred = "¬" := rfl

theorem encAtom_injective {a b : Atom} (h : encAtom a = encAtom b) : a = b := by
  cases a; cases b
  simp only [encAtom, Atom.mk.injEq, List.cons.injEq, true_and] at h
  simp [h.1, h.2]

@[simp] theorem encAtom_inj_iff {a b : Atom} : encAtom a = encAtom b ↔ a = b :=
  ⟨encAtom_injective, fun h => by rw [h]⟩

/-- The encoding of a literal: a negative literal becomes the positive literal on the
complementary atom. -/
def encLit : Lit → Lit
  | .pos a => .pos a
  | .neg a => .pos (encAtom a)

theorem encLit_isPos (l : Lit) : (encLit l).IsPos := by
  cases l <;> simp [encLit, Lit.IsPos]

/-! ### The transformation -/

/-- The reserved predicate name `"¬"` does not occur in the task. -/
def NegFresh (T : GroundTask) : Prop := ∀ a ∈ T.atoms, a.pred ≠ "¬"

/-- Executable check for `GroundTask.NegFresh`. -/
def negFreshB (T : GroundTask) : Bool := T.atoms.all (fun a => a.pred != "¬")

theorem negFreshB_iff {T : GroundTask} : T.negFreshB = true ↔ T.NegFresh := by
  simp only [negFreshB, List.all_eq_true, bne_iff_ne, ne_eq, NegFresh]

/-- The operator of the positive normal form: negative preconditions are replaced by the
complementary atoms, and the complementary atoms are maintained by the effect. -/
def encOp (op : GroundOp) : GroundOp where
  action := op.action
  pre := op.pre.map encLit
  effs := [⟨[], op.addList ++ (op.delList.filter (fun a => decide (a ∉ op.addList))).map encAtom,
    op.delList ++ op.addList.map encAtom⟩]
  cost := op.cost

@[simp] theorem encOp_action (op : GroundOp) : (encOp op).action = op.action := rfl

@[simp] theorem encOp_cost (op : GroundOp) : (encOp op).cost = op.cost := rfl

theorem encOp_unconditional (op : GroundOp) : (encOp op).Unconditional := by
  intro ce hce
  simp only [encOp, List.mem_singleton] at hce
  subst hce
  rfl

theorem encOp_positive (op : GroundOp) : (encOp op).Positive := by
  refine ⟨?_, ?_⟩
  · intro l hl
    obtain ⟨l', -, rfl⟩ := List.mem_map.1 hl
    exact encLit_isPos l'
  · intro ce hce l hl
    simp only [encOp, List.mem_singleton] at hce
    subst hce
    cases hl

/-- The positive normal form of a ground task. -/
def toPositive (T : GroundTask) : GroundTask where
  ops := T.ops.map encOp
  init := T.init ++ (T.atoms.filter (fun a => decide (a ∉ T.init))).map encAtom
  goal := T.goal.map (fun c => c.map encLit)

theorem toPositive_unconditional (T : GroundTask) : T.toPositive.Unconditional := by
  intro op hop
  obtain ⟨op', -, rfl⟩ := List.mem_map.1 hop
  exact encOp_unconditional op'

theorem toPositive_positive (T : GroundTask) : T.toPositive.Positive := by
  refine ⟨?_, ?_⟩
  · intro op hop
    obtain ⟨op', -, rfl⟩ := List.mem_map.1 hop
    exact encOp_positive op'
  · intro c hc l hl
    obtain ⟨c', -, rfl⟩ := List.mem_map.1 hc
    obtain ⟨l', -, rfl⟩ := List.mem_map.1 hl
    exact encLit_isPos l'

theorem toPositive_conjunctiveGoal {T : GroundTask} (h : T.ConjunctiveGoal) :
    T.toPositive.ConjunctiveGoal := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c.map encLit, by simp [toPositive, hc]⟩

/-- The positive normal form of an unconditional task with a conjunctive goal can be
translated to STRIPS. -/
theorem toPositive_stripsReady {T : GroundTask} (hc : T.ConjunctiveGoal) :
    T.toPositive.StripsReady :=
  ⟨toPositive_unconditional T, toPositive_positive T, toPositive_conjunctiveGoal hc⟩

/-! ### The state encoding -/

/-- The state of the positive task corresponding to a state of the original task: the
complementary atoms of exactly the atoms of the task that are false in `s`. -/
def encState (T : GroundTask) (s : State) : State :=
  s ∪ {b | ∃ a ∈ T.atoms, a ∉ s ∧ b = encAtom a}

/-- A state that only contains atoms of the task. -/
def Clean (T : GroundTask) (s : State) : Prop := ∀ a ∈ s, a ∈ T.atoms

theorem clean_initState (T : GroundTask) : T.Clean T.initState :=
  fun _ ha => mem_atoms_of_mem_init ha

theorem Clean.result {T : GroundTask} {op : GroundOp} (hop : op ∈ T.ops) {s : State}
    (hs : T.Clean s) : T.Clean (op.result s) := by
  intro a ha
  rcases GroundOp.mem_result.1 ha with hadd | ⟨hmem, -⟩
  · obtain ⟨ce, hce, -, hmem⟩ := hadd
    exact mem_atoms_of_mem_op hop (GroundOp.mem_atomList_of_mem_add hce hmem)
  · exact hs a hmem

theorem encAtom_not_mem_of_clean {T : GroundTask} (hfresh : T.NegFresh) {s : State}
    (hs : T.Clean s) (a : Atom) : encAtom a ∉ s := by
  intro h
  exact hfresh _ (hs _ h) rfl

theorem mem_encState_of_mem_atoms {T : GroundTask} (hfresh : T.NegFresh) {s : State}
    {a : Atom} (ha : a ∈ T.atoms) : a ∈ T.encState s ↔ a ∈ s := by
  simp only [encState, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro (h | ⟨b, -, -, rfl⟩)
    · exact h
    · exact absurd rfl (hfresh _ ha)
  · exact Or.inl

theorem encAtom_mem_encState {T : GroundTask} (hfresh : T.NegFresh) {s : State}
    (hs : T.Clean s) {a : Atom} (ha : a ∈ T.atoms) :
    encAtom a ∈ T.encState s ↔ a ∉ s := by
  simp only [encState, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro (h | ⟨b, -, hb, heq⟩)
    · exact absurd h (encAtom_not_mem_of_clean hfresh hs a)
    · have hab : a = b := encAtom_injective heq
      subst hab
      exact hb
  · intro h
    exact Or.inr ⟨a, ha, h, rfl⟩

/-! ### Conditions are preserved -/

theorem encLit_holds {T : GroundTask} (hfresh : T.NegFresh) {s : State} (hs : T.Clean s)
    {l : Lit} (hl : l.atom ∈ T.atoms) : (encLit l).Holds (T.encState s) ↔ l.Holds s := by
  cases l with
  | pos a => exact mem_encState_of_mem_atoms hfresh hl
  | neg a => exact encAtom_mem_encState hfresh hs hl

theorem encClause_holds {T : GroundTask} (hfresh : T.NegFresh) {s : State} (hs : T.Clean s)
    {c : List Lit} (hc : ∀ l ∈ c, l.atom ∈ T.atoms) :
    ClauseHolds (c.map encLit) (T.encState s) ↔ ClauseHolds c s := by
  simp only [ClauseHolds, List.mem_map]
  constructor
  · intro h l hl
    exact (encLit_holds hfresh hs (hc l hl)).1 (h _ ⟨l, hl, rfl⟩)
  · rintro h l' ⟨l, hl, rfl⟩
    exact (encLit_holds hfresh hs (hc l hl)).2 (h l hl)

theorem applicable_encOp_iff {T : GroundTask} (hfresh : T.NegFresh) {s : State}
    (hs : T.Clean s) {op : GroundOp} (hop : op ∈ T.ops) :
    (encOp op).Applicable (T.encState s) ↔ op.Applicable s := by
  refine encClause_holds hfresh hs (fun l hl => ?_)
  exact mem_atoms_of_mem_op hop (GroundOp.mem_atomList_of_mem_pre hl)

theorem toPositive_goalHolds {T : GroundTask} (hfresh : T.NegFresh) {s : State}
    (hs : T.Clean s) : T.toPositive.GoalHolds (T.encState s) ↔ T.GoalHolds s := by
  simp only [GoalHolds, toPositive, DnfHolds, List.mem_map]
  constructor
  · rintro ⟨c', ⟨c, hc, rfl⟩, hcl⟩
    exact ⟨c, hc, (encClause_holds hfresh hs
      (fun l hl => mem_atoms_of_mem_goal hc hl)).1 hcl⟩
  · rintro ⟨c, hc, hcl⟩
    exact ⟨c.map encLit, ⟨c, hc, rfl⟩, (encClause_holds hfresh hs
      (fun l hl => mem_atoms_of_mem_goal hc hl)).2 hcl⟩

/-! ### The initial state and the successor states -/

theorem toPositive_initState {T : GroundTask} : T.toPositive.initState = T.encState T.initState := by
  ext a
  simp only [initState, toPositive, encState, Set.mem_setOf_eq, Set.mem_union,
    List.mem_append, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro (h | ⟨b, ⟨hb, hb'⟩, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨b, hb, hb', rfl⟩
  · rintro (h | ⟨b, hb, hb', rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨b, ⟨hb, hb'⟩, rfl⟩

theorem encOp_addList (op : GroundOp) :
    (encOp op).addList =
      op.addList ++ (op.delList.filter (fun a => decide (a ∉ op.addList))).map encAtom := by
  simp [GroundOp.addList, encOp]

theorem encOp_delList (op : GroundOp) :
    (encOp op).delList = op.delList ++ op.addList.map encAtom := by
  simp [GroundOp.delList, encOp]

theorem encOp_addSet {op : GroundOp} (s : State) :
    (encOp op).addSet s =
      {a | a ∈ op.addList} ∪ {b | ∃ a ∈ op.delList, a ∉ op.addList ∧ b = encAtom a} := by
  rw [GroundOp.addSet_of_unconditional (encOp_unconditional op)]
  ext b
  simp only [encOp_addList, Set.mem_setOf_eq, Set.mem_union, List.mem_append, List.mem_map,
    List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro (h | ⟨a, ⟨ha, ha'⟩, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨a, ha, ha', rfl⟩
  · rintro (h | ⟨a, ha, ha', rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨a, ⟨ha, ha'⟩, rfl⟩

theorem encOp_delSet {op : GroundOp} (s : State) :
    (encOp op).delSet s =
      {a | a ∈ op.delList} ∪ {b | ∃ a ∈ op.addList, b = encAtom a} := by
  rw [GroundOp.delSet_of_unconditional (encOp_unconditional op)]
  ext b
  simp only [encOp_delList, Set.mem_setOf_eq, Set.mem_union, List.mem_append, List.mem_map]
  constructor
  · rintro (h | ⟨a, ha, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨a, ha, rfl⟩
  · rintro (h | ⟨a, ha, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨a, ha, rfl⟩

/-- The successor state agrees under the state encoding. -/
theorem encState_result {T : GroundTask} (hfresh : T.NegFresh) (huc : T.Unconditional)
    {s : State} (hs : T.Clean s) {op : GroundOp} (hop : op ∈ T.ops) :
    (encOp op).result (T.encState s) = T.encState (op.result s) := by
  have hadd : ∀ a ∈ op.addList, a ∈ T.atoms := fun a ha =>
    mem_atoms_of_mem_op hop (GroundOp.mem_atomList_of_mem_addList ha)
  have hdel : ∀ a ∈ op.delList, a ∈ T.atoms := fun a ha =>
    mem_atoms_of_mem_op hop (GroundOp.mem_atomList_of_mem_delList ha)
  have hres : ∀ a : Atom, a ∈ op.result s ↔ a ∈ op.addList ∨ (a ∈ s ∧ a ∉ op.delList) := by
    intro a
    simp only [GroundOp.mem_result, GroundOp.addSet_of_unconditional (huc op hop),
      GroundOp.delSet_of_unconditional (huc op hop), Set.mem_setOf_eq]
  ext b
  constructor
  · intro hb
    rcases GroundOp.mem_result.1 hb with hb' | ⟨hb', hb''⟩
    · -- `b` is added by the encoded operator
      rw [encOp_addSet] at hb'
      rcases hb' with hb' | ⟨a, ha, ha', rfl⟩
      · -- a plain atom that is added
        refine Or.inl ?_
        exact (hres b).2 (Or.inl hb')
      · -- a complementary atom for an atom that is deleted and not added
        refine Or.inr ⟨a, hdel a ha, ?_, rfl⟩
        intro hmem
        rcases (hres a).1 hmem with h | ⟨-, h⟩
        · exact ha' h
        · exact h ha
    · rw [encOp_delSet] at hb''
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_and] at hb''
      obtain ⟨hb1, hb2⟩ := hb''
      rcases hb' with hb' | ⟨a, ha, ha', rfl⟩
      · -- a plain atom of `s` that is not deleted
        exact Or.inl ((hres b).2 (Or.inr ⟨hb', hb1⟩))
      · -- a complementary atom that survives
        refine Or.inr ⟨a, ha, ?_, rfl⟩
        intro hmem
        rcases (hres a).1 hmem with h | ⟨h, -⟩
        · exact hb2 a h rfl
        · exact ha' h
  · intro hb
    rcases hb with hb | ⟨a, ha, ha', rfl⟩
    · -- a plain atom of the successor state
      rcases (hres b).1 hb with hadd' | ⟨hmem, hnd⟩
      · refine GroundOp.mem_result.2 (Or.inl ?_)
        rw [encOp_addSet]
        exact Or.inl hadd'
      · refine GroundOp.mem_result.2 (Or.inr ⟨Or.inl hmem, ?_⟩)
        rw [encOp_delSet]
        simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_and]
        refine ⟨hnd, ?_⟩
        intro c hc heq
        exact hfresh b (hs b hmem) (heq ▸ rfl)
    · -- a complementary atom of the successor state
      have hna : a ∉ op.addList := fun h => ha' ((hres a).2 (Or.inl h))
      by_cases hd : a ∈ op.delList
      · refine GroundOp.mem_result.2 (Or.inl ?_)
        rw [encOp_addSet]
        exact Or.inr ⟨a, hd, hna, rfl⟩
      · have hns : a ∉ s := fun h => ha' ((hres a).2 (Or.inr ⟨h, hd⟩))
        refine GroundOp.mem_result.2 (Or.inr ⟨Or.inr ⟨a, ha, hns, rfl⟩, ?_⟩)
        rw [encOp_delSet]
        simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_and]
        constructor
        · intro h
          exact hfresh _ (hdel _ h) rfl
        · rintro c hc heq
          exact hna (encAtom_inj_iff.1 heq.symm ▸ hc)

/-! ### Executions and plans -/

theorem Execution.clean {T : GroundTask} {s s' : State} {π : List GroundOp}
    (h : T.Execution s π s') (hs : T.Clean s) : T.Clean s' := by
  induction h with
  | nil s => exact hs
  | cons hop _ _ ih => exact ih (hs.result hop)

theorem toPositive_execution {T : GroundTask} (hfresh : T.NegFresh) (huc : T.Unconditional)
    {s s' : State} {π : List GroundOp} (hs : T.Clean s) (h : T.Execution s π s') :
    T.toPositive.Execution (T.encState s) (π.map encOp) (T.encState s') := by
  induction h with
  | nil s => exact Execution.nil _
  | @cons s s' op π hop happ hexec ih =>
    refine Execution.cons (List.mem_map_of_mem hop)
      ((applicable_encOp_iff hfresh hs hop).2 happ) ?_
    rw [encState_result hfresh huc hs hop]
    exact ih (hs.result hop)

theorem execution_of_toPositive_execution {T : GroundTask} (hfresh : T.NegFresh)
    (huc : T.Unconditional) :
    ∀ {S S' : State} {π' : List GroundOp}, T.toPositive.Execution S π' S' →
      ∀ s : State, T.Clean s → S = T.encState s →
        ∃ (π : List GroundOp) (s' : State), π' = π.map encOp ∧ T.Execution s π s' ∧
          S' = T.encState s' := by
  intro S S' π' h
  induction h with
  | nil S => intro s _ hS; exact ⟨[], s, rfl, Execution.nil s, hS⟩
  | @cons S S' op' π' hop' happ' hexec ih =>
    intro s hs hS
    obtain ⟨op, hop, rfl⟩ := List.mem_map.1 hop'
    subst hS
    have happ : op.Applicable s := (applicable_encOp_iff hfresh hs hop).1 happ'
    have hres : (encOp op).result (T.encState s) = T.encState (op.result s) :=
      encState_result hfresh huc hs hop
    obtain ⟨π, s', rfl, hexec', hS'⟩ := ih (op.result s) (hs.result hop) hres
    exact ⟨op :: π, s', rfl, Execution.cons hop happ hexec', hS'⟩

/-- **The positive normal form preserves plans** (soundness direction): a plan of the
original task, with every operator compiled, is a plan of the positive task. -/
theorem toPositive_isPlan {T : GroundTask} (hfresh : T.NegFresh) (huc : T.Unconditional)
    {π : List GroundOp} (h : T.IsPlan π) : T.toPositive.IsPlan (π.map encOp) := by
  obtain ⟨s, hexec, hgoal⟩ := h
  refine ⟨T.encState s, ?_, ?_⟩
  · rw [toPositive_initState]
    exact toPositive_execution hfresh huc (clean_initState T) hexec
  · exact (toPositive_goalHolds hfresh (hexec.clean (clean_initState T))).2 hgoal

/-- **The positive normal form preserves plans** (completeness direction): every plan of
the positive task is the compilation of a plan of the original task. -/
theorem isPlan_of_toPositive_isPlan {T : GroundTask} (hfresh : T.NegFresh)
    (huc : T.Unconditional) {π' : List GroundOp} (h : T.toPositive.IsPlan π') :
    ∃ π : List GroundOp, π' = π.map encOp ∧ T.IsPlan π := by
  obtain ⟨S, hexec, hgoal⟩ := h
  rw [toPositive_initState] at hexec
  obtain ⟨π, s', rfl, hexec', rfl⟩ :=
    execution_of_toPositive_execution hfresh huc hexec T.initState (clean_initState T) rfl
  exact ⟨π, rfl, s', hexec',
    (toPositive_goalHolds hfresh (hexec'.clean (clean_initState T))).1 hgoal⟩

/-- The compilation does not change the underlying ground actions of a plan, so a plan of
the positive task can be read back as a plan of the PDDL instance. -/
@[simp] theorem map_action_map_encOp (π : List GroundOp) :
    (π.map encOp).map (·.action) = π.map (·.action) := by
  simp [List.map_map, Function.comp_def]

/-- The compilation does not change plan costs. -/
@[simp] theorem planCost_map_encOp (π : List GroundOp) :
    planCost (π.map encOp) = planCost π := by
  simp [planCost, List.map_map, Function.comp_def]

/-- **The positive normal form preserves solvability.** -/
theorem toPositive_solvable_iff {T : GroundTask} (hfresh : T.NegFresh)
    (huc : T.Unconditional) : T.toPositive.Solvable ↔ T.Solvable := by
  constructor
  · rintro ⟨π', hπ'⟩
    obtain ⟨π, -, hπ⟩ := isPlan_of_toPositive_isPlan hfresh huc hπ'
    exact ⟨π, hπ⟩
  · rintro ⟨π, hπ⟩
    exact ⟨_, toPositive_isPlan hfresh huc hπ⟩

end GroundTask

/-- **Grounding a PDDL instance, compiling it to positive normal form and translating it
to the STRIPS interface preserves solvability.** -/
theorem groundInstance_positive_strips_solvable_iff {I : Instance}
    (hwf : I.domain.typesWellFormedB = true) {T : GroundTask}
    (h : groundInstance I = some T) (hfresh : T.NegFresh) (huc : T.Unconditional)
    (hgoal : T.ConjunctiveGoal) :
    Nonempty (STRIPS.PlanningTask.Plan T.toPositive.toSTRIPS T.toPositive.toSTRIPS.init) ↔
      I.Solvable := by
  rw [GroundTask.strips_solvable_iff (GroundTask.toPositive_stripsReady hgoal),
    GroundTask.toPositive_solvable_iff hfresh huc, groundInstance_solvable_iff hwf h]

end PDDL
