import pddl.Grounding.Positive

/-!
# Removing conditional effects from a ground task

The grounder of `pddl.Grounding.Compile` produces operators with *conditional* effects,
because PDDL (`:adl`) has them.  The STRIPS interface of the `planning` library has not, and
the positive normal form of `pddl.Grounding.Positive` is only defined for unconditional
tasks, so a ground task with conditional effects could not be solved by the grounded route
at all.

This module implements the standard *expansion* of conditional effects and proves that it
preserves the semantics.  An operator `op` with conditional effects `e₁, …, eₖ` is replaced
by one operator per "trigger pattern": for every subset `S ⊆ {e₁, …, eₖ}` there is an
operator whose precondition is that of `op` together with the conditions of the effects in
`S` and, for every effect not in `S`, the negation of *one* literal of its condition (a
conjunctive condition is falsified by falsifying one of its literals, and the choice is part
of the pattern), and whose effect is the unconditional union of the effects in `S`.  The
expansion is computed by `PDDL.GroundOp.expandEffs`, which enumerates exactly these
patterns; it is exponential in the number of conditional effects of the operator, which is
unavoidable for this compilation (the polynomial alternatives change the plan length).

Note that the expansion introduces *negative* preconditions even if the task had none, so it
has to be run **before** the positive normal form, not after.  The atoms of the task are not
changed (`PDDL.GroundTask.mem_atoms_toUnconditional`), so in particular `NegFresh` survives
and the positive normal form can be applied afterwards.

The main results, for a ground task `T`:

* `PDDL.GroundTask.toUnconditional_unconditional`: the compiled task has no conditional
  effects (and `toUnconditional_conjunctiveGoal`, `toUnconditional_negFresh`: the goal and
  the atoms are unchanged);
* `PDDL.GroundTask.toUnconditional_isPlan` and
  `PDDL.GroundTask.isPlan_of_toUnconditional_isPlan`: the plans of the two tasks correspond
  one operator at a time, with the same underlying ground actions and the same cost;
* `PDDL.GroundTask.toUnconditional_solvable_iff`: solvability is preserved.
-/

namespace PDDL

namespace GroundOp

/-- One trigger pattern of a list of conditional effects: the extra condition `cond` under
which exactly the effects of the pattern fire, and the atoms `add`/`del` those effects add
and delete. -/
structure Expansion where
  /-- The extra condition characterising the pattern. -/
  cond : List Lit
  /-- The atoms added by the effects that fire. -/
  add : List Atom
  /-- The atoms deleted by the effects that fire. -/
  del : List Atom
  deriving DecidableEq, Repr, Inhabited

/-- A conjunction of literals is consistent if it does not contain a literal together with
its complement.  Inconsistent patterns are dropped during the expansion: they can never be
applicable, and pruning them is what keeps the expansion of an operator whose effect
conditions share literals small. -/
def consistentB (c : List Lit) : Bool := c.all (fun l => !c.contains l.complement)

theorem consistentB_of_clauseHolds {c : List Lit} {s : State} (h : ClauseHolds c s) :
    consistentB c = true := by
  simp only [consistentB, List.all_eq_true, Bool.not_eq_true']
  intro l hl
  have hmem : l.complement ∉ c := fun hmem =>
    (Lit.holds_complement.1 (h _ hmem)) (h l hl)
  simp [hmem]

/-- All trigger patterns of a list of conditional effects.  For the head effect `e` there
are two kinds of pattern: `e` fires (its condition is added to the pattern's condition and
its atoms to the pattern's effect), or `e` does not fire, which is witnessed by the negation
of one of the literals of its condition — so an effect with an empty condition always
fires.  Patterns with an inconsistent condition are dropped, which is sound because such an
operator would never be applicable. -/
def expandEffs : List CondEff → List Expansion
  | [] => [⟨[], [], []⟩]
  | e :: es =>
      (expandEffs es).flatMap (fun t =>
        (⟨e.cond ++ t.cond, e.add ++ t.add, e.del ++ t.del⟩ ::
          e.cond.map (fun l => ⟨l.complement :: t.cond, t.add, t.del⟩)).filter
            (fun t' => consistentB t'.cond))

/-- In a state satisfying the condition of a pattern, the pattern adds exactly what the
conditional effects add. -/
theorem mem_expandEffs_add_iff {es : List CondEff} {t : Expansion} (ht : t ∈ expandEffs es)
    {s : State} (hc : ClauseHolds t.cond s) (a : Atom) :
    a ∈ t.add ↔ ∃ e ∈ es, e.Triggered s ∧ a ∈ e.add := by
  induction es generalizing t with
  | nil =>
    simp only [expandEffs, List.mem_singleton] at ht
    subst ht
    simp
  | cons e es ih =>
    simp only [expandEffs, List.mem_flatMap, List.mem_filter, List.mem_cons,
      List.mem_map] at ht
    obtain ⟨t', ht', hcase, -⟩ := ht
    rcases hcase with rfl | ⟨l, hl, rfl⟩
    · -- `e` fires
      simp only at hc ⊢
      rw [clauseHolds_append] at hc
      have hrec := ih ht' hc.2
      simp only [List.mem_append, hrec, List.mem_cons, CondEff.Triggered]
      constructor
      · rintro (h | ⟨e', he', htr, ha⟩)
        · exact ⟨e, Or.inl rfl, hc.1, h⟩
        · exact ⟨e', Or.inr he', htr, ha⟩
      · rintro ⟨e', (rfl | he'), htr, ha⟩
        · exact Or.inl ha
        · exact Or.inr ⟨e', he', htr, ha⟩
    · -- `e` does not fire
      simp only [clauseHolds_cons] at hc
      have hnot : ¬ e.Triggered s := by
        intro htr
        exact (Lit.holds_complement.1 hc.1) (htr l hl)
      have hrec := ih ht' hc.2
      simp only [hrec, List.mem_cons]
      constructor
      · rintro ⟨e', he', htr, ha⟩
        exact ⟨e', Or.inr he', htr, ha⟩
      · rintro ⟨e', (rfl | he'), htr, ha⟩
        · exact absurd htr hnot
        · exact ⟨e', he', htr, ha⟩

/-- In a state satisfying the condition of a pattern, the pattern deletes exactly what the
conditional effects delete. -/
theorem mem_expandEffs_del_iff {es : List CondEff} {t : Expansion} (ht : t ∈ expandEffs es)
    {s : State} (hc : ClauseHolds t.cond s) (a : Atom) :
    a ∈ t.del ↔ ∃ e ∈ es, e.Triggered s ∧ a ∈ e.del := by
  induction es generalizing t with
  | nil =>
    simp only [expandEffs, List.mem_singleton] at ht
    subst ht
    simp
  | cons e es ih =>
    simp only [expandEffs, List.mem_flatMap, List.mem_filter, List.mem_cons,
      List.mem_map] at ht
    obtain ⟨t', ht', hcase, -⟩ := ht
    rcases hcase with rfl | ⟨l, hl, rfl⟩
    · simp only at hc ⊢
      rw [clauseHolds_append] at hc
      have hrec := ih ht' hc.2
      simp only [List.mem_append, hrec, List.mem_cons, CondEff.Triggered]
      constructor
      · rintro (h | ⟨e', he', htr, ha⟩)
        · exact ⟨e, Or.inl rfl, hc.1, h⟩
        · exact ⟨e', Or.inr he', htr, ha⟩
      · rintro ⟨e', (rfl | he'), htr, ha⟩
        · exact Or.inl ha
        · exact Or.inr ⟨e', he', htr, ha⟩
    · simp only [clauseHolds_cons] at hc
      have hnot : ¬ e.Triggered s := by
        intro htr
        exact (Lit.holds_complement.1 hc.1) (htr l hl)
      have hrec := ih ht' hc.2
      simp only [hrec, List.mem_cons]
      constructor
      · rintro ⟨e', he', htr, ha⟩
        exact ⟨e', Or.inr he', htr, ha⟩
      · rintro ⟨e', (rfl | he'), htr, ha⟩
        · exact absurd htr hnot
        · exact ⟨e', he', htr, ha⟩

/-- Every state satisfies the condition of one of the patterns. -/
theorem exists_expandEffs_cond (es : List CondEff) (s : State) :
    ∃ t ∈ expandEffs es, ClauseHolds t.cond s := by
  classical
  induction es with
  | nil => exact ⟨⟨[], [], []⟩, by simp [expandEffs], by simp⟩
  | cons e es ih =>
    obtain ⟨t', ht', hc'⟩ := ih
    by_cases htr : ∀ l ∈ e.cond, l.Holds s
    · refine ⟨⟨e.cond ++ t'.cond, e.add ++ t'.add, e.del ++ t'.del⟩, ?_, ?_⟩
      · have hcons : ClauseHolds (e.cond ++ t'.cond) s :=
          clauseHolds_append.2 ⟨htr, hc'⟩
        simp only [expandEffs, List.mem_flatMap, List.mem_filter, List.mem_cons]
        exact ⟨t', ht', Or.inl rfl, consistentB_of_clauseHolds hcons⟩
      · simpa [clauseHolds_append] using ⟨htr, hc'⟩
    · push Not at htr
      obtain ⟨l, hl, hnl⟩ := htr
      have hcons : ClauseHolds (l.complement :: t'.cond) s :=
        clauseHolds_cons.2 ⟨Lit.holds_complement.2 hnl, hc'⟩
      refine ⟨⟨l.complement :: t'.cond, t'.add, t'.del⟩, ?_, hcons⟩
      simp only [expandEffs, List.mem_flatMap, List.mem_filter, List.mem_cons,
        List.mem_map]
      exact ⟨t', ht', Or.inr ⟨l, hl, rfl⟩, consistentB_of_clauseHolds hcons⟩

/-- The atoms of the extra condition of a pattern are atoms of the effect conditions. -/
theorem exists_cond_of_mem_expandEffs_cond {es : List CondEff} {t : Expansion}
    (ht : t ∈ expandEffs es) {l : Lit} (hl : l ∈ t.cond) :
    ∃ e ∈ es, ∃ l' ∈ e.cond, l.atom = l'.atom := by
  induction es generalizing t with
  | nil =>
    simp only [expandEffs, List.mem_singleton] at ht
    subst ht
    simp at hl
  | cons e es ih =>
    simp only [expandEffs, List.mem_flatMap, List.mem_filter, List.mem_cons,
      List.mem_map] at ht
    obtain ⟨t', ht', hcase, -⟩ := ht
    rcases hcase with rfl | ⟨l₀, hl₀, rfl⟩
    · simp only [List.mem_append] at hl
      rcases hl with hl | hl
      · exact ⟨e, List.mem_cons_self, l, hl, rfl⟩
      · obtain ⟨e', he', l', hl', heq⟩ := ih ht' hl
        exact ⟨e', List.mem_cons_of_mem _ he', l', hl', heq⟩
    · simp only [List.mem_cons] at hl
      rcases hl with rfl | hl
      · refine ⟨e, List.mem_cons_self, l₀, hl₀, ?_⟩
        cases l₀ <;> simp [Lit.complement]
      · obtain ⟨e', he', l', hl', heq⟩ := ih ht' hl
        exact ⟨e', List.mem_cons_of_mem _ he', l', hl', heq⟩

/-- The atoms added by a pattern are added by one of the effects. -/
theorem exists_add_of_mem_expandEffs_add {es : List CondEff} {t : Expansion}
    (ht : t ∈ expandEffs es) {a : Atom} (ha : a ∈ t.add) : ∃ e ∈ es, a ∈ e.add := by
  induction es generalizing t with
  | nil =>
    simp only [expandEffs, List.mem_singleton] at ht
    subst ht
    simp at ha
  | cons e es ih =>
    simp only [expandEffs, List.mem_flatMap, List.mem_filter, List.mem_cons,
      List.mem_map] at ht
    obtain ⟨t', ht', hcase, -⟩ := ht
    rcases hcase with rfl | ⟨l₀, hl₀, rfl⟩
    · simp only [List.mem_append] at ha
      rcases ha with ha | ha
      · exact ⟨e, List.mem_cons_self, ha⟩
      · obtain ⟨e', he', ha'⟩ := ih ht' ha
        exact ⟨e', List.mem_cons_of_mem _ he', ha'⟩
    · obtain ⟨e', he', ha'⟩ := ih ht' ha
      exact ⟨e', List.mem_cons_of_mem _ he', ha'⟩

/-- The atoms deleted by a pattern are deleted by one of the effects. -/
theorem exists_del_of_mem_expandEffs_del {es : List CondEff} {t : Expansion}
    (ht : t ∈ expandEffs es) {a : Atom} (ha : a ∈ t.del) : ∃ e ∈ es, a ∈ e.del := by
  induction es generalizing t with
  | nil =>
    simp only [expandEffs, List.mem_singleton] at ht
    subst ht
    simp at ha
  | cons e es ih =>
    simp only [expandEffs, List.mem_flatMap, List.mem_filter, List.mem_cons,
      List.mem_map] at ht
    obtain ⟨t', ht', hcase, -⟩ := ht
    rcases hcase with rfl | ⟨l₀, hl₀, rfl⟩
    · simp only [List.mem_append] at ha
      rcases ha with ha | ha
      · exact ⟨e, List.mem_cons_self, ha⟩
      · obtain ⟨e', he', ha'⟩ := ih ht' ha
        exact ⟨e', List.mem_cons_of_mem _ he', ha'⟩
    · obtain ⟨e', he', ha'⟩ := ih ht' ha
      exact ⟨e', List.mem_cons_of_mem _ he', ha'⟩

/-! ### The expanded operators -/

/-- The unconditional operator belonging to one trigger pattern of `op`. -/
def expandOne (op : GroundOp) (t : Expansion) : GroundOp where
  action := op.action
  pre := op.pre ++ t.cond
  effs := [⟨[], t.add, t.del⟩]
  cost := op.cost

@[simp] theorem expandOne_action (op : GroundOp) (t : Expansion) :
    (op.expandOne t).action = op.action := rfl

@[simp] theorem expandOne_cost (op : GroundOp) (t : Expansion) :
    (op.expandOne t).cost = op.cost := rfl

theorem expandOne_unconditional (op : GroundOp) (t : Expansion) :
    (op.expandOne t).Unconditional := by
  intro ce hce
  simp only [expandOne, List.mem_singleton] at hce
  subst hce
  rfl

/-- The unconditional operators an operator with conditional effects is replaced by. -/
def expand (op : GroundOp) : List GroundOp := (expandEffs op.effs).map op.expandOne

theorem mem_expand_iff {op op' : GroundOp} :
    op' ∈ op.expand ↔ ∃ t ∈ expandEffs op.effs, op.expandOne t = op' := by
  simp [expand, eq_comm]

@[simp] theorem action_of_mem_expand {op op' : GroundOp} (h : op' ∈ op.expand) :
    op'.action = op.action := by
  obtain ⟨t, -, rfl⟩ := mem_expand_iff.1 h
  rfl

@[simp] theorem cost_of_mem_expand {op op' : GroundOp} (h : op' ∈ op.expand) :
    op'.cost = op.cost := by
  obtain ⟨t, -, rfl⟩ := mem_expand_iff.1 h
  rfl

theorem unconditional_of_mem_expand {op op' : GroundOp} (h : op' ∈ op.expand) :
    op'.Unconditional := by
  obtain ⟨t, -, rfl⟩ := mem_expand_iff.1 h
  exact expandOne_unconditional op t

/-- An expanded operator is applicable only where the original operator is. -/
theorem applicable_of_mem_expand {op op' : GroundOp} (h : op' ∈ op.expand) {s : State}
    (happ : op'.Applicable s) : op.Applicable s := by
  obtain ⟨t, -, rfl⟩ := mem_expand_iff.1 h
  exact (clauseHolds_append.1 happ).1

/-- Where an expanded operator is applicable, it has the same successor state as the
original operator. -/
theorem result_of_mem_expand {op op' : GroundOp} (h : op' ∈ op.expand) {s : State}
    (happ : op'.Applicable s) : op'.result s = op.result s := by
  obtain ⟨t, ht, rfl⟩ := mem_expand_iff.1 h
  have hc : ClauseHolds t.cond s := (clauseHolds_append.1 happ).2
  have hadd : (op.expandOne t).addSet s = op.addSet s := by
    ext a
    rw [addSet_of_unconditional (expandOne_unconditional op t)]
    simp only [Set.mem_setOf_eq, addList, expandOne, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, addSet]
    rw [mem_expandEffs_add_iff ht hc a]
  have hdel : (op.expandOne t).delSet s = op.delSet s := by
    ext a
    rw [delSet_of_unconditional (expandOne_unconditional op t)]
    simp only [Set.mem_setOf_eq, delList, expandOne, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, delSet]
    rw [mem_expandEffs_del_iff ht hc a]
  simp only [result, hadd, hdel]

/-- Wherever the original operator is applicable, one of its expansions is. -/
theorem exists_mem_expand_applicable {op : GroundOp} {s : State} (happ : op.Applicable s) :
    ∃ op' ∈ op.expand, op'.Applicable s := by
  obtain ⟨t, ht, hc⟩ := exists_expandEffs_cond op.effs s
  refine ⟨op.expandOne t, mem_expand_iff.2 ⟨t, ht, rfl⟩, ?_⟩
  exact clauseHolds_append.2 ⟨happ, hc⟩

theorem expandOne_atomList (op : GroundOp) (t : Expansion) :
    (op.expandOne t).atomList
      = (op.pre ++ t.cond).map Lit.atom ++ (t.add ++ t.del) := by
  simp [atomList, preAtoms, expandOne]

/-- The expansion does not introduce new atoms. -/
theorem mem_atomList_of_mem_expand {op op' : GroundOp} (h : op' ∈ op.expand) {a : Atom}
    (ha : a ∈ op'.atomList) : a ∈ op.atomList := by
  obtain ⟨t, ht, rfl⟩ := mem_expand_iff.1 h
  rw [expandOne_atomList] at ha
  simp only [List.map_append, List.mem_append, List.mem_map] at ha
  rcases ha with (⟨l, hl, rfl⟩ | ⟨l, hl, rfl⟩) | ha | ha
  · exact mem_atomList_of_mem_pre hl
  · obtain ⟨e, he, l', hl', heq⟩ := exists_cond_of_mem_expandEffs_cond ht hl
    rw [heq]
    exact mem_atomList_of_mem_cond he hl'
  · obtain ⟨e, he, ha'⟩ := exists_add_of_mem_expandEffs_add ht ha
    exact mem_atomList_of_mem_add he ha'
  · obtain ⟨e, he, ha'⟩ := exists_del_of_mem_expandEffs_del ht ha
    exact mem_atomList_of_mem_del he ha'

end GroundOp

/-! ### The compiled task -/

namespace GroundTask

/-- The ground task with all conditional effects expanded away. -/
def toUnconditional (T : GroundTask) : GroundTask where
  ops := T.ops.flatMap GroundOp.expand
  init := T.init
  goal := T.goal

@[simp] theorem toUnconditional_init (T : GroundTask) : T.toUnconditional.init = T.init := rfl

@[simp] theorem toUnconditional_goal (T : GroundTask) : T.toUnconditional.goal = T.goal := rfl

@[simp] theorem toUnconditional_initState (T : GroundTask) :
    T.toUnconditional.initState = T.initState := rfl

@[simp] theorem toUnconditional_goalHolds (T : GroundTask) (s : State) :
    T.toUnconditional.GoalHolds s ↔ T.GoalHolds s := Iff.rfl

theorem mem_toUnconditional_ops {T : GroundTask} {op' : GroundOp}
    (h : op' ∈ T.toUnconditional.ops) : ∃ op ∈ T.ops, op' ∈ op.expand :=
  List.mem_flatMap.1 h

theorem mem_toUnconditional_ops_of {T : GroundTask} {op op' : GroundOp} (hop : op ∈ T.ops)
    (h : op' ∈ op.expand) : op' ∈ T.toUnconditional.ops :=
  List.mem_flatMap.2 ⟨op, hop, h⟩

/-- **The compiled task has no conditional effects.** -/
theorem toUnconditional_unconditional (T : GroundTask) : T.toUnconditional.Unconditional := by
  intro op' hop'
  obtain ⟨op, -, h⟩ := mem_toUnconditional_ops hop'
  exact GroundOp.unconditional_of_mem_expand h

theorem toUnconditional_conjunctiveGoal {T : GroundTask} (h : T.ConjunctiveGoal) :
    T.toUnconditional.ConjunctiveGoal := h

/-- The expansion does not introduce new atoms. -/
theorem mem_atoms_toUnconditional {T : GroundTask} {a : Atom}
    (h : a ∈ T.toUnconditional.atoms) : a ∈ T.atoms := by
  rcases mem_atoms.1 h with hi | ⟨c, hc, hgoal⟩ | ⟨op', hop', hop⟩
  · exact mem_atoms_of_mem_init hi
  · simp only [List.mem_map] at hgoal
    obtain ⟨l, hl, rfl⟩ := hgoal
    exact mem_atoms_of_mem_goal hc hl
  · obtain ⟨op, hopT, hexp⟩ := mem_toUnconditional_ops hop'
    exact mem_atoms_of_mem_op hopT (GroundOp.mem_atomList_of_mem_expand hexp hop)

theorem toUnconditional_negFresh {T : GroundTask} (h : T.NegFresh) :
    T.toUnconditional.NegFresh :=
  fun _ ha => h _ (mem_atoms_toUnconditional ha)

/-! ### Executions and plans -/

theorem toUnconditional_execution {T : GroundTask} {s s' : State} {π : List GroundOp}
    (h : T.Execution s π s') :
    ∃ π' : List GroundOp, T.toUnconditional.Execution s π' s' ∧
      π'.map (·.action) = π.map (·.action) ∧ planCost π' = planCost π := by
  induction h with
  | nil s => exact ⟨[], Execution.nil s, rfl, rfl⟩
  | @cons s s' op π hop happ _ ih =>
    obtain ⟨π', hexec, hact, hcost⟩ := ih
    obtain ⟨op', hexp, happ'⟩ := GroundOp.exists_mem_expand_applicable happ
    refine ⟨op' :: π', ?_, ?_, ?_⟩
    · refine Execution.cons (mem_toUnconditional_ops_of hop hexp) happ' ?_
      rw [GroundOp.result_of_mem_expand hexp happ']
      exact hexec
    · simp [hact, GroundOp.action_of_mem_expand hexp]
    · simp [planCost] at hcost ⊢
      simp [hcost, GroundOp.cost_of_mem_expand hexp]

theorem execution_of_toUnconditional_execution {T : GroundTask} {s s' : State}
    {π' : List GroundOp} (h : T.toUnconditional.Execution s π' s') :
    ∃ π : List GroundOp, T.Execution s π s' ∧
      π.map (·.action) = π'.map (·.action) ∧ planCost π = planCost π' := by
  induction h with
  | nil s => exact ⟨[], Execution.nil s, rfl, rfl⟩
  | @cons s s' op' π' hop' happ' _ ih =>
    obtain ⟨op, hop, hexp⟩ := mem_toUnconditional_ops hop'
    have happ : op.Applicable s := GroundOp.applicable_of_mem_expand hexp happ'
    have hres : op'.result s = op.result s := GroundOp.result_of_mem_expand hexp happ'
    rw [hres] at ih
    obtain ⟨π, hexec, hact, hcost⟩ := ih
    refine ⟨op :: π, Execution.cons hop happ hexec, ?_, ?_⟩
    · simp [hact, GroundOp.action_of_mem_expand hexp]
    · simp [planCost] at hcost ⊢
      simp [hcost, GroundOp.cost_of_mem_expand hexp]

/-- **The expansion preserves plans** (soundness direction). -/
theorem toUnconditional_isPlan {T : GroundTask} {π : List GroundOp} (h : T.IsPlan π) :
    ∃ π' : List GroundOp, T.toUnconditional.IsPlan π' ∧
      π'.map (·.action) = π.map (·.action) ∧ planCost π' = planCost π := by
  obtain ⟨s, hexec, hgoal⟩ := h
  obtain ⟨π', hexec', hact, hcost⟩ := toUnconditional_execution hexec
  exact ⟨π', ⟨s, hexec', hgoal⟩, hact, hcost⟩

/-- **The expansion preserves plans** (completeness direction). -/
theorem isPlan_of_toUnconditional_isPlan {T : GroundTask} {π' : List GroundOp}
    (h : T.toUnconditional.IsPlan π') :
    ∃ π : List GroundOp, T.IsPlan π ∧
      π.map (·.action) = π'.map (·.action) ∧ planCost π = planCost π' := by
  obtain ⟨s, hexec, hgoal⟩ := h
  obtain ⟨π, hexec', hact, hcost⟩ := execution_of_toUnconditional_execution hexec
  exact ⟨π, ⟨s, hexec', hgoal⟩, hact, hcost⟩

/-- **The expansion preserves solvability.** -/
theorem toUnconditional_solvable_iff (T : GroundTask) :
    T.toUnconditional.Solvable ↔ T.Solvable := by
  constructor
  · rintro ⟨π', hπ'⟩
    obtain ⟨π, hπ, -, -⟩ := isPlan_of_toUnconditional_isPlan hπ'
    exact ⟨π, hπ⟩
  · rintro ⟨π, hπ⟩
    obtain ⟨π', hπ', -, -⟩ := toUnconditional_isPlan hπ
    exact ⟨π', hπ'⟩

end GroundTask

end PDDL
