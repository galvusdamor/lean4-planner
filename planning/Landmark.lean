import planning.DeleteRelaxation
import planning.Planner
import Mathlib.Tactic.Cases
import Mathlib.Tactic.NormNum

namespace Validator

instance STRIPS.actions.decidableMem {n : ℕ} (prob : STRIPS n) (a : Action n) :
    Decidable (a ∈ prob.actions) :=
  Finset.decidableMem a prob.actions'.toFinset

def Path.actionsUsed {n : ℕ} {pt : STRIPS n} {s s' : State n} : Path pt s s' → List (Action n)
  | Path.empty _ => []
  | Path.cons a _ _ _ p => a :: p.actionsUsed

instance Path.instMembership {n : ℕ} {pt : STRIPS n} {s s' : State n} :
    Membership (Action n) (Path pt s s') where
  mem p a := a ∈ p.actionsUsed

-- should mean to test whether the action a is one of the action in the plan
instance STRIPS.plan.action.membership {n : ℕ} (prob : STRIPS n) (s : State n) :
    Membership (Action n) (Plan prob s) where
  mem plan a := @Membership.mem _ _ Path.instMembership plan.path a


def is_disjunctive_action_landmark_for_state {n : ℕ} (prob : STRIPS n) (lm : List (Action n))
    (s : State' n) : Prop :=
  lm.all (fun a => decide (a ∈ prob.actions)) ∧
    (∀ plan : Plan prob (convertState s), ∃ a ∈ lm, a ∈ plan)


-- remove all actions mentioned in lm
def remove_actions {n : ℕ} (prob : STRIPS n) (lm : List (Action n)) : STRIPS n :=
  let actions : Actions' n := prob.actions'.filter (fun a' => a' ∉ lm)
  STRIPS.mk prob.varNames actions prob.init' prob.goal'

def set_init {n : ℕ} (prob : STRIPS n) (s : State' n) : STRIPS n :=
  STRIPS.mk prob.varNames prob.actions' s prob.goal'


-- alternative characterisation of landmarks: if you remove the action, the problem must now be
-- unsolvable
def action_set_removal_implies_unsolvable_for_state {n : ℕ} (prob : STRIPS n)
    (lm : List (Action n)) (s : State' n) : Prop :=
  lm.all (fun a => decide (a ∈ prob.actions)) ∧
    (Unsolvable (set_init (remove_actions prob lm) s))

private lemma mem_remove_actions_of_not_mem_lm {n : ℕ} (prob : STRIPS n) (lm : List (Action n))
    (a : Action n) (ha : a ∈ prob.actions') (ha_lm : a ∉ lm) :
    a ∈ (remove_actions prob lm).actions' := by
  unfold remove_actions
  simp_all only [decide_not, List.mem_filter, decide_false, Bool.not_false, and_self]

private lemma mem_of_mem_remove_actions {n : ℕ} (prob : STRIPS n) (lm : List (Action n))
    (a : Action n) (ha : a ∈ (remove_actions prob lm).actions') :
    a ∈ prob.actions' ∧ a ∉ lm := by
  unfold remove_actions at ha
  simp_all (config := { singlePass := true }) only [decide_not, List.mem_filter, true_and,
    Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, not_false_eq_true]

private lemma path_remove_to_path_orig {n : ℕ} (prob : STRIPS n) (lm : List (Action n))
    (s : State' n) {s1 s2 : State n}
    (p : Path (set_init (remove_actions prob lm) s) s1 s2) :
    ∃ p' : Path prob s1 s2, p'.actionsUsed.Sublist p.actionsUsed ∧
      (∀ a, a ∈ p'.actionsUsed → a ∉ lm) ∧ p'.cost = p.cost := by
  induction' p with a s1 s2 ha p' hp'
  · exact ⟨Path.empty a, by tauto⟩
  · rename_i h₁ h₂ h₃
    obtain ⟨p'', hp'', hp'''⟩ := h₃
    use Path.cons s1 ha (show s1 ∈ prob.actions from by
      simp_all [set_init, remove_actions]
      simp_all [STRIPS.actions]) h₁ p''
    simp_all [Path.actionsUsed, Path.cost]
    unfold set_init at hp'; simp_all [remove_actions]
    unfold STRIPS.actions at hp'
    simp_all only [List.toFinset_filter, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not, Finset.coe_filter, List.mem_toFinset, Set.mem_setOf_eq, not_false_eq_true]

private lemma plan_remove_to_plan_orig {n : ℕ} (prob : STRIPS n) (lm : List (Action n))
    (s : State' n)
    (plan : Plan (set_init (remove_actions prob lm) s) (convertState s)) :
    ∃ plan' : Plan prob (convertState s), ∀ a, a ∈ plan'.path.actionsUsed → a ∉ lm := by
  cases' path_remove_to_path_orig prob lm s plan.path with p' hp'
  cases' plan with last p goal
  exact ⟨⟨last, p', goal⟩, hp'.2.1⟩

private lemma path_orig_to_path_remove {n : ℕ} (prob : STRIPS n) (lm : List (Action n))
    (s : State' n) {s1 s2 : State n}
    (p : Path prob s1 s2) (h : ∀ a, a ∈ p.actionsUsed → a ∉ lm) :
    ∃ p' : Path (set_init (remove_actions prob lm) s) s1 s2, p'.cost = p.cost := by
  induction p <;> simp_all [Path.cost]
  · exact ⟨Path.empty _, rfl⟩
  · rename_i a s1 s2 ha succ π ih
    obtain ⟨p', hp'⟩ := ih (fun a ha => h a <| List.mem_cons_of_mem _ ha)
    refine' ⟨Path.cons _ _ _ _ p', _⟩
    exact ‹Action n›
    all_goals simp_all [set_init, remove_actions]
    all_goals norm_num [Path.actionsUsed, Path.cost] at *
    · simp_all [STRIPS.actions]
    · exact And.imp_right (fun a_2 => rfl) succ
    · exact hp'

private lemma plan_orig_to_plan_remove {n : ℕ} (prob : STRIPS n) (lm : List (Action n))
    (s : State' n)
    (plan : Plan prob (convertState s)) (h : ∀ a, a ∈ plan.path.actionsUsed → a ∉ lm) :
    Nonempty (Plan (set_init (remove_actions prob lm) s) (convertState s)) := by
  obtain ⟨p', hp'⟩ := path_orig_to_path_remove prob lm s plan.path h
  exact ⟨⟨_, p', plan.goal⟩⟩

lemma disjunctive_action_landmarks_iff_unsolvability {n : ℕ} (prob : STRIPS n)
    (lm : List (Action n)) (s : State' n) :
    is_disjunctive_action_landmark_for_state prob lm s ↔
      action_set_removal_implies_unsolvable_for_state prob lm s := by
  constructor <;> intro h
  · refine ⟨h.1, ?_⟩
    contrapose! h
    obtain ⟨plan⟩ := h
    obtain ⟨plan', hplan'⟩ := plan_remove_to_plan_orig prob lm s plan
    unfold is_disjunctive_action_landmark_for_state
    simp_all only [List.all_eq_true, decide_eq_true_eq, not_and, not_forall, not_exists]
    intro a
    apply Exists.intro
    · intro x a_1
      apply Aesop.BuiltinRules.not_intro
      intro a_2
      apply hplan'
      · exact a_2
      · exact a_1
  · refine ⟨h.1, ?_⟩
    intro plan
    contrapose! h
    simp [action_set_removal_implies_unsolvable_for_state]
    exact fun _ => plan_orig_to_plan_remove prob lm s plan fun a ha => by
      apply Aesop.BuiltinRules.not_intro
      intro a_1
      apply h
      on_goal 2 => exact ha
      · simp_all only

instance STRIPS.unsolvability.decidable {n : ℕ} (prob : STRIPS n) :
    Decidable (Unsolvable prob) := by
  cases h : planner prob (fun _ => 0) with
  | none => exact isTrue (planner_complete prob (fun _ => 0) h)
  | some plan => exact isFalse (fun ⟨f⟩ => f plan)

instance STRIPS.landmark.decidable {n : ℕ} (prob : STRIPS n) (lm : List (Action n))
    (s : State' n) :
    Decidable (is_disjunctive_action_landmark_for_state prob lm s) := by
  rw [disjunctive_action_landmarks_iff_unsolvability]
  unfold action_set_removal_implies_unsolvable_for_state
  exact instDecidableAnd

-- delete relaxation landmark
def is_delete_relaxed_disjunctive_action_landmark_for_state {n : ℕ} (prob : STRIPS n)
    (lm : List (Action n)) (s : State' n) : Prop :=
  lm.all (fun a => decide ((delete_relax_action a) ∈ (delete_relaxation prob).actions)) ∧
    (∀ plan : Plan (delete_relaxation prob) (convertState s), ∃ a ∈ lm, (delete_relax_action a) ∈ plan)


/-- A disjunctive action landmark of the delete relaxation is exactly a set of actions whose
removal makes the delete relaxation unsolvable. -/
lemma disjunctive_action_landmarks_of_delete_relax_iff_unsolvability_of_delete_relax {n : ℕ} (prob : STRIPS n)
    (lm : List (Action n)) (s : State' n) :
    is_disjunctive_action_landmark_for_state (delete_relaxation prob) lm s ↔
      action_set_removal_implies_unsolvable_for_state (delete_relaxation prob) lm s :=
  disjunctive_action_landmarks_iff_unsolvability (delete_relaxation prob) lm s

/-- A delete relaxed disjunction action landmark is exactly a set of actions that if removed from the
delete relaxation makes the problem unsolvable. Note that we project the actions to their delete
relaxed versions in the condition. -/
lemma delete_relaxed_disjunctive_action_landmarks_iff_unsolvability_of_delete_relax {n : ℕ} (prob : STRIPS n)
    (lm : List (Action n)) (s : State' n) :
    is_delete_relaxed_disjunctive_action_landmark_for_state prob lm s ↔
      action_set_removal_implies_unsolvable_for_state (delete_relaxation prob)
      (lm.map (fun a => delete_relax_action a)) s := by
        convert disjunctive_action_landmarks_of_delete_relax_iff_unsolvability_of_delete_relax prob ( List.map ( fun a => delete_relax_action a ) lm ) s using 1
        simp [ is_delete_relaxed_disjunctive_action_landmark_for_state, is_disjunctive_action_landmark_for_state, List.all_map ]

/-- Relaxing a path: every path of the original task, started from a (pointwise) larger state,
can be replayed in the delete relaxation using the delete-relaxed versions of the same actions,
reaching a state that is again at least as large.  Delete relaxation only ever adds variables, so
larger starting states keep all actions applicable and keep the reached states larger. -/
lemma relax_path {n : ℕ} (prob : STRIPS n) {s1 s2 : State n} (p : Path prob s1 s2)
    {t1 : State n} (hsub : s1 ⊆ t1) :
    ∃ (t2 : State n), s2 ⊆ t2 ∧
      ∃ (q : Path (delete_relaxation prob) t1 t2),
        q.actionsUsed = p.actionsUsed.map delete_relax_action := by
  revert t1
  induction' p with a s1 s2 ha succ π ih
  · exact fun { t1 } ht1 => ⟨ t1, ht1, Path.empty _, rfl ⟩
  · rename_i h₁ h₂
    intro t1 ht1
    obtain ⟨t1', ht1', ht1'_succ⟩ : ∃ t1', Successor (delete_relax_action s1) t1 t1' ∧ s1.add ⊆ t1' ∧ t1 ⊆ t1' := by
      refine' ⟨ t1 ∪ s1.add, _, _, _ ⟩ <;> simp_all [ Successor, Applicable ]
      simp_all [ delete_relax_action ]
      simp_all [ Action.pre, Action.add, Action.del, Set.subset_def ]
      simp [ convertVarSet ]
    obtain ⟨t2, ht2, q, hq⟩ := h₂ (by
    grind : ha ⊆ t1')
    use t2, ht2, Path.cons (delete_relax_action s1) t1' (by
    simp_all [ STRIPS.actions, delete_relaxation ]
    exact ⟨ s1, π, rfl ⟩) (by
    exact ht1') q
    simp [ Path.actionsUsed, hq ]

/-- Every original plan uses an action whose delete relaxation is one of the landmark's relaxed
actions.

The naive statement
`is_delete_relaxed_disjunctive_action_landmark_for_state prob lm s →`
`  is_disjunctive_action_landmark_for_state prob lm s`
does not hold: its conclusion would require an action `a ∈ lm` to occur verbatim in every original
plan, but delete relaxation forgets delete effects, so the action witnessed by a relaxed plan is
only determined up to its relaxation. The naive version is kept below for reference.
lemma delete_relaxation_landmarks_are_landmarks {n : ℕ} (prob : STRIPS n) (lm : List (Action n))
(s : State' n):
is_delete_relaxed_disjunctive_action_landmark_for_state prob lm s →
is_disjunctive_action_landmark_for_state prob lm s
-/
lemma delete_relaxation_landmarks_have_landmark_property {n : ℕ} (prob : STRIPS n) (lm : List (Action n))
    (s : State' n) :
    is_delete_relaxed_disjunctive_action_landmark_for_state prob lm s →
      ∀ plan : Plan prob (convertState s),
        ∃ a ∈ plan, delete_relax_action a ∈ lm.map delete_relax_action := by
  intro h plan
  obtain ⟨t2, ht2, q, hq⟩ := relax_path prob plan.path (le_refl _)
  -- By definition of `is_delete_relaxed_disjunctive_action_landmark_for_state`, we know that `t2` satisfies the goal.
  have ht2_goal : (delete_relaxation prob).GoalState t2 := by
    exact Set.Subset.trans plan.goal ht2
  obtain ⟨a, ha⟩ : ∃ a ∈ lm, delete_relax_action a ∈ q.actionsUsed := by
    exact h.2 ⟨ t2, q, ht2_goal ⟩
  obtain ⟨a', ha'⟩ : ∃ a' ∈ plan.path.actionsUsed, delete_relax_action a' = delete_relax_action a := by
    grind
  exact ⟨ a', by simpa [ Path.instMembership ] using ha'.1, by
    simp_all only [List.mem_map]
    obtain ⟨left, right⟩ := ha
    obtain ⟨left_1, right_1⟩ := ha'
    obtain ⟨w, h_1⟩ := right
    obtain ⟨left_2, right⟩ := h_1
    apply Exists.intro
    · apply And.intro
      on_goal 2 => rfl
      · simp_all only ⟩



def get_all_equiv_delete_relaxed_actions {n : ℕ} (prob : STRIPS n) (lm : List (Action n)) : List (Action n) :=
  prob.actions'.filter (fun a => lm.any (fun l => delete_relax_action a = delete_relax_action l))

/-
stronger statement: if the actions a ∈ lm are actually part of the original problem, then if lm is part of every delete relaxed plan, then it must be part of any plan. The reasoning is that the set of all delete-relaxed plans is a "superset" (not in the strict sende due to missing deleting effects) of all plans. I.e. for every actual plan there is an equivalent delete relaxed one that contains an action a ∈ lm thus the actual plan must too. The proof here succeeds as all the actions a ∈ lm are part of prob and those are the only actions in plans
-/
lemma delete_relaxation_landmarks_are_landmarks {n : ℕ} (prob : STRIPS n) (lm : List (Action n))
  (action_all_exist : lm.all (fun a => decide (a ∈ prob.actions)))
    (s : State' n) :
    is_delete_relaxed_disjunctive_action_landmark_for_state prob lm s →
      is_disjunctive_action_landmark_for_state prob (get_all_equiv_delete_relaxed_actions prob lm) s := by
        intro h
        refine' ⟨ _, _ ⟩
        · simp_all [ List.all_eq_true, get_all_equiv_delete_relaxed_actions ]
          exact fun x hx => Or.inr <| by simpa [ STRIPS.actions ] using hx
        · intro plan
          have := delete_relaxation_landmarks_have_landmark_property prob lm s h plan
          obtain ⟨ a, ha₁, ha₂ ⟩ := this; use a; simp_all [ get_all_equiv_delete_relaxed_actions ]
          exact ⟨ by
            have h_mem : ∀ {s1 s2 : State n} {p : Path prob s1 s2}, ∀ a ∈ p.actionsUsed, a ∈ prob.actions' := by
              intros s1 s2 p a ha; induction p <;> simp_all [ Path.actionsUsed ]
              unfold STRIPS.actions at *
              rename_i succ π π_ih
              simp_all only [List.coe_toFinset, Set.mem_setOf_eq]
              obtain ⟨w, h_1⟩ := ha₂
              obtain ⟨left, right⟩ := succ
              obtain ⟨left_1, right_1⟩ := h_1
              subst right
              cases ha with
              | inl h_1 =>
                subst h_1
                simp_all only [implies_true]
              | inr h_2 => simp_all only [forall_const]
            exact h_mem a ha₁, by obtain ⟨ b, hb₁, hb₂ ⟩ := ha₂; exact ⟨ b, hb₁, hb₂.symm ⟩ ⟩

/-- Characterisation of membership in the relax-equivalence closure of a landmark: an action is in
the closure iff it is a genuine action of the problem that is delete-relaxation equivalent to some
landmark action. -/
lemma mem_get_all_equiv_iff {n : ℕ} (prob : STRIPS n) (lm : List (Action n)) (a : Action n) :
    a ∈ get_all_equiv_delete_relaxed_actions prob lm ↔
      a ∈ prob.actions' ∧ ∃ l ∈ lm, delete_relax_action a = delete_relax_action l := by
  unfold get_all_equiv_delete_relaxed_actions
  simp [List.mem_filter, List.any_eq_true]

/-- Each action of the relax-equivalence closure is a genuine action of the problem. -/
lemma mem_actions_of_mem_get_all_equiv {n : ℕ} (prob : STRIPS n) (lm : List (Action n))
    {a : Action n} (ha : a ∈ get_all_equiv_delete_relaxed_actions prob lm) : a ∈ prob.actions' :=
  ((mem_get_all_equiv_iff prob lm a).mp ha).1

/-- An action of the relax-equivalence closure shares the cost of one of the landmark's actions
(delete relaxation preserves costs). -/
lemma cost_eq_of_mem_get_all_equiv {n : ℕ} (prob : STRIPS n) (lm : List (Action n))
    {a : Action n} (ha : a ∈ get_all_equiv_delete_relaxed_actions prob lm) :
    ∃ l ∈ lm, a.cost = l.cost := by
  obtain ⟨-, l, hl, he⟩ := (mem_get_all_equiv_iff prob lm a).mp ha
  exact ⟨l, hl, by have := congrArg Action.cost he; simpa [delete_relax_action] using this⟩

/-- A landmark action that is a genuine action of the problem belongs to its own
relax-equivalence closure. -/
lemma mem_get_all_equiv_of_mem {n : ℕ} (prob : STRIPS n) (lm : List (Action n))
    {a : Action n} (ha : a ∈ lm) (ha' : a ∈ prob.actions') :
    a ∈ get_all_equiv_delete_relaxed_actions prob lm :=
  (mem_get_all_equiv_iff prob lm a).mpr ⟨ha', a, ha, rfl⟩

--- elementary landmark heuristic
def elementary_landmark_heuristic {n : ℕ} (prob : STRIPS n) (lm : List (Action n))
    (s : State' n) : ℕ :=
  if is_disjunctive_action_landmark_for_state prob lm s then
    if lm_empty : lm = [] then (2 ^ n) * max_action_cost prob
    else
      (lm.map (fun a => a.cost)).min
        (by simp_all only [ne_eq, List.map_eq_nil_iff, not_false_eq_true])
  else 0

/-
Every action appearing in a `Path` is a member of the problem's action set.
-/
private lemma action_in_path_mem_actions {n : ℕ} {pt : STRIPS n} {s s' : State n}
    (p : Path pt s s') (a : Action n) (ha : a ∈ p.actionsUsed) : a ∈ pt.actions := by
  induction' p with a' s2 ha' succ p' ih generalizing a
  · cases ha
  · cases ha
    · simp_all only
    · rename_i succ_1 π π_ih a_1
      obtain ⟨left, right⟩ := succ_1
      subst right
      apply π_ih
      exact a_1

/-
The cost of a `Path` is at least the cost of any single action used in it.
-/
private lemma path_cost_ge_action_cost {n : ℕ} {pt : STRIPS n} {s s' : State n}
    (p : Path pt s s') (a : Action n) (ha : a ∈ p.actionsUsed) : p.cost ≥ a.cost := by
  induction' p with a' s2 ha' succ p' ih generalizing a
  · cases ha
  · cases ha <;> simp_all [ Path.cost ]
    exact le_add_right ( by solve_by_elim )

lemma elementary_landmark_heuristic_is_admissible {n : ℕ} (prob : STRIPS n)
    (lm : List (Action n)) :
    heur_admissible prob (elementary_landmark_heuristic prob lm) := by
  intro s plan; by_cases h : is_disjunctive_action_landmark_for_state prob lm s <;> by_cases h' : lm = [] <;> simp_all
  · have := h.2 plan
    subst h'
    simp_all only [List.not_mem_nil, false_and, exists_false]
  · have h_cost_le : ∃ a ∈ lm, a ∈ plan := by exact h.2 plan
    obtain ⟨ a, ha₁, ha₂ ⟩ := h_cost_le
    have := path_cost_ge_action_cost plan.path a ha₂
    simp_all [ elementary_landmark_heuristic ]
    exact le_trans ( List.min_le_of_mem ( List.mem_map.mpr ⟨ a, ha₁, rfl ⟩ ) ) this
  · unfold elementary_landmark_heuristic
    subst h'
    simp_all only [↓reduceIte, zero_le]
  · unfold elementary_landmark_heuristic
    simp_all only [↓reduceIte, zero_le]

/-- Every action appearing in a `Path` is a member of the problem's action set. -/
lemma mem_actions_of_mem_actionsUsed {n : ℕ} {pt : STRIPS n} {s s' : State n}
    (p : Path pt s s') {a : Action n} (ha : a ∈ p.actionsUsed) : a ∈ pt.actions :=
  action_in_path_mem_actions p a ha

/-- The cost of a `Path` is the sum of the costs of the actions it uses. -/
lemma path_cost_eq_sum_actionsUsed {n : ℕ} {pt : STRIPS n} {s s' : State n}
    (p : Path pt s s') : p.cost = (p.actionsUsed.map (fun a => a.cost)).sum := by
  induction p with
  | empty s => rfl
  | cons a s2 ha succ p' ih => simp [Path.cost, Path.actionsUsed, ih, Nat.add_comm]

end Validator