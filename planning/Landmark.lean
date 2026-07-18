import planning.DeleteRelaxation
import planning.Planner
import Mathlib.Tactic.Cases
import Mathlib.Tactic.NormNum

namespace STRIPS

instance PlanningTask.actions.decidableMem {n : ℕ} (prob : PlanningTask n) (a : Action n) :
    Decidable (a ∈ prob.actions) :=
  Finset.decidableMem a prob.actions'.toFinset

def Path.actionsUsed {n : ℕ} {pt : PlanningTask n} {s s' : State n} : Path pt s s' → List (Action n)
  | Path.empty _ => []
  | Path.cons a _ _ _ p => a :: p.actionsUsed

instance Path.instMembership {n : ℕ} {pt : PlanningTask n} {s s' : State n} :
    Membership (Action n) (Path pt s s') where
  mem p a := a ∈ p.actionsUsed

-- should mean to test whether the action a is one of the action in the plan
instance PlanningTask.plan.action.membership {n : ℕ} (prob : PlanningTask n) (s : State n) :
    Membership (Action n) (Plan prob s) where
  mem plan a := @Membership.mem _ _ Path.instMembership plan.path a


def is_disjunctive_action_landmark_for_state {n : ℕ} (prob : PlanningTask n) (lm : List (Action n))
    (s : State' n) : Prop :=
  lm.all (fun a => decide (a ∈ prob.actions)) ∧
    (∀ plan : Plan prob (convertState s), ∃ a ∈ lm, a ∈ plan)


-- remove all actions mentioned in lm
def remove_actions {n : ℕ} (prob : PlanningTask n) (lm : List (Action n)) : PlanningTask n :=
  let actions : List (Action n) := prob.actions'.filter (fun a' => a' ∉ lm)
  PlanningTask.mk prob.varNames actions prob.init' prob.goal'

def set_init {n : ℕ} (prob : PlanningTask n) (s : State' n) : PlanningTask n :=
  PlanningTask.mk prob.varNames prob.actions' s prob.goal'


-- alternative characterisation of landmarks: if you remove the action, the problem must now be
-- unsolvable
def action_set_removal_implies_unsolvable_for_state {n : ℕ} (prob : PlanningTask n)
    (lm : List (Action n)) (s : State' n) : Prop :=
  lm.all (fun a => decide (a ∈ prob.actions)) ∧
    (Unsolvable (set_init (remove_actions prob lm) s))

private lemma mem_remove_actions_of_not_mem_lm {n : ℕ} (prob : PlanningTask n) (lm : List (Action n))
    (a : Action n) (ha : a ∈ prob.actions') (ha_lm : a ∉ lm) :
    a ∈ (remove_actions prob lm).actions' := by
  unfold remove_actions
  simp_all only [decide_not, List.mem_filter, decide_false, Bool.not_false, and_self]

private lemma mem_of_mem_remove_actions {n : ℕ} (prob : PlanningTask n) (lm : List (Action n))
    (a : Action n) (ha : a ∈ (remove_actions prob lm).actions') :
    a ∈ prob.actions' ∧ a ∉ lm := by
  unfold remove_actions at ha
  simp_all (config := { singlePass := true }) only [decide_not, List.mem_filter, true_and,
    Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, not_false_eq_true]

private lemma path_remove_to_path_orig {n : ℕ} (prob : PlanningTask n) (lm : List (Action n))
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
      simp_all [PlanningTask.actions]) h₁ p''
    simp_all [Path.actionsUsed, Path.cost]
    unfold set_init at hp'; simp_all [remove_actions]
    unfold PlanningTask.actions at hp'
    simp_all only [List.toFinset_filter, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not, Finset.coe_filter, List.mem_toFinset, Set.mem_setOf_eq, not_false_eq_true]

private lemma plan_remove_to_plan_orig {n : ℕ} (prob : PlanningTask n) (lm : List (Action n))
    (s : State' n)
    (plan : Plan (set_init (remove_actions prob lm) s) (convertState s)) :
    ∃ plan' : Plan prob (convertState s), ∀ a, a ∈ plan'.path.actionsUsed → a ∉ lm := by
  cases' path_remove_to_path_orig prob lm s plan.path with p' hp'
  cases' plan with last p goal
  exact ⟨⟨last, p', goal⟩, hp'.2.1⟩

private lemma path_orig_to_path_remove {n : ℕ} (prob : PlanningTask n) (lm : List (Action n))
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
    · simp_all [PlanningTask.actions]
    · exact And.imp_right (fun a_2 => rfl) succ
    · exact hp'

private lemma plan_orig_to_plan_remove {n : ℕ} (prob : PlanningTask n) (lm : List (Action n))
    (s : State' n)
    (plan : Plan prob (convertState s)) (h : ∀ a, a ∈ plan.path.actionsUsed → a ∉ lm) :
    Nonempty (Plan (set_init (remove_actions prob lm) s) (convertState s)) := by
  obtain ⟨p', hp'⟩ := path_orig_to_path_remove prob lm s plan.path h
  exact ⟨⟨_, p', plan.goal⟩⟩

lemma disjunctive_action_landmarks_iff_unsolvability {n : ℕ} (prob : PlanningTask n)
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

instance PlanningTask.unsolvability.decidable {n : ℕ} (prob : PlanningTask n) :
    Decidable (Unsolvable prob) := by
  cases h : planner prob (fun _ => 0) with
  | none => exact isTrue (planner_complete prob (fun _ => 0) (zero_heur_admissible' _) h)
  | some plan => exact isFalse (fun ⟨f⟩ => f plan)

instance PlanningTask.landmark.decidable {n : ℕ} (prob : PlanningTask n) (lm : List (Action n))
    (s : State' n) :
    Decidable (is_disjunctive_action_landmark_for_state prob lm s) := by
  rw [disjunctive_action_landmarks_iff_unsolvability]
  unfold action_set_removal_implies_unsolvable_for_state
  exact instDecidableAnd

-- delete relaxation landmark
def is_delete_relaxed_disjunctive_action_landmark_for_state {n : ℕ} (prob : PlanningTask n)
    (lm : List (Action n)) (s : State' n) : Prop :=
  lm.all (fun a => decide ((delete_relax_action a) ∈ (delete_relaxation prob).actions)) ∧
    (∀ plan : Plan (delete_relaxation prob) (convertState s), ∃ a ∈ lm, (delete_relax_action a) ∈ plan)


/-- A disjunctive action landmark of the delete relaxation is exactly a set of actions whose
removal makes the delete relaxation unsolvable. -/
lemma disjunctive_action_landmarks_of_delete_relax_iff_unsolvability_of_delete_relax {n : ℕ} (prob : PlanningTask n)
    (lm : List (Action n)) (s : State' n) :
    is_disjunctive_action_landmark_for_state (delete_relaxation prob) lm s ↔
      action_set_removal_implies_unsolvable_for_state (delete_relaxation prob) lm s :=
  disjunctive_action_landmarks_iff_unsolvability (delete_relaxation prob) lm s

/-- A delete relaxed disjunction action landmark is exactly a set of actions that if removed from the
delete relaxation makes the problem unsolvable. Note that we project the actions to their delete
relaxed versions in the condition. -/
lemma delete_relaxed_disjunctive_action_landmarks_iff_unsolvability_of_delete_relax {n : ℕ} (prob : PlanningTask n)
    (lm : List (Action n)) (s : State' n) :
    is_delete_relaxed_disjunctive_action_landmark_for_state prob lm s ↔
      action_set_removal_implies_unsolvable_for_state (delete_relaxation prob)
      (lm.map (fun a => delete_relax_action a)) s := by
        convert disjunctive_action_landmarks_of_delete_relax_iff_unsolvability_of_delete_relax prob ( List.map ( fun a => delete_relax_action a ) lm ) s using 1
        simp [ is_delete_relaxed_disjunctive_action_landmark_for_state, is_disjunctive_action_landmark_for_state, List.all_map ]

/-
Relaxing a path: every path of the original task, started from a (pointwise) larger state,
can be replayed in the delete relaxation using the delete-relaxed versions of the same actions,
reaching a state that is again at least as large.  Delete relaxation only ever adds variables, so
larger starting states keep all actions applicable and keep the reached states larger.
-/
lemma relax_path {n : ℕ} (prob : PlanningTask n) {s1 s2 : State n} (p : Path prob s1 s2)
    {t1 : State n} (hsub : s1 ⊆ t1) :
    ∃ (t2 : State n), s2 ⊆ t2 ∧
      ∃ (q : Path (delete_relaxation prob) t1 t2),
        q.actionsUsed = p.actionsUsed.map delete_relax_action := by
  -- We'll use induction on the path `p` to construct the desired path `q`.
  induction' p with a s1 s2 ha succ π ih generalizing t1;
  · exact ⟨ t1, hsub, Path.empty t1, rfl ⟩;
  · rename_i h₁ h₂;
    obtain ⟨ t2, ht2, q, hq ⟩ := h₂ ( show ha ⊆ t1 ∪ s1.add from fun i => by cases ih ; aesop );
    refine' ⟨ t2, ht2, Path.cons _ _ _ _ q, _ ⟩;
    exact delete_relax_action s1;
    all_goals norm_num [ Path.actionsUsed, delete_relax_action ];
    · simp +decide [ delete_relaxation, PlanningTask.actions ];
      exact ⟨ s1, by simpa [ PlanningTask.actions ] using π, rfl ⟩;
    · constructor;
      · grind;
      · ext; simp [delete_relax_action];
    · exact hq

/-
Every original plan uses an action whose delete relaxation is one of the landmark's relaxed
actions.

The naive statement
`is_delete_relaxed_disjunctive_action_landmark_for_state prob lm s →`
`  is_disjunctive_action_landmark_for_state prob lm s`
does not hold: its conclusion would require an action `a ∈ lm` to occur verbatim in every original
plan, but delete relaxation forgets delete effects, so the action witnessed by a relaxed plan is
only determined up to its relaxation. The naive version is kept below for reference.
lemma delete_relaxation_landmarks_are_landmarks {n : ℕ} (prob : PlanningTask n) (lm : List (Action n))
(s : State' n):
is_delete_relaxed_disjunctive_action_landmark_for_state prob lm s →
is_disjunctive_action_landmark_for_state prob lm s
-/
lemma delete_relaxation_landmarks_have_landmark_property {n : ℕ} (prob : PlanningTask n) (lm : List (Action n))
    (s : State' n) :
    is_delete_relaxed_disjunctive_action_landmark_for_state prob lm s →
      ∀ plan : Plan prob (convertState s),
        ∃ a ∈ plan, delete_relax_action a ∈ lm.map delete_relax_action := by
          intro h plan;
          have := h.2;
          obtain ⟨ t2, ht2, q, hq ⟩ := relax_path prob plan.path ( le_refl ( convertState s ) );
          obtain ⟨ a, ha₁, ha₂ ⟩ := this ⟨ t2, q, by
            exact fun x hx => ht2 <| plan.goal hx ⟩
          generalize_proofs at *;
          simp_all +decide [ Membership.mem, Path.actionsUsed ];
          obtain ⟨ b, hb₁, hb₂ ⟩ := List.mem_map.mp ha₂;
          exact ⟨ b, hb₁, List.mem_map.mpr ⟨ a, ha₁, hb₂ ▸ rfl ⟩ ⟩

def get_all_equiv_delete_relaxed_actions {n : ℕ} (prob : PlanningTask n) (lm : List (Action n)) : List (Action n) :=
  prob.actions'.filter (fun a => lm.any (fun l => delete_relax_action a = delete_relax_action l))

/-
stronger statement: if the actions a ∈ lm are actually part of the original problem, then if lm is part of every delete relaxed plan, then it must be part of any plan. The reasoning is that the set of all delete-relaxed plans is a "superset" (not in the strict sende due to missing deleting effects) of all plans. I.e. for every actual plan there is an equivalent delete relaxed one that contains an action a ∈ lm thus the actual plan must too. The proof here succeeds as all the actions a ∈ lm are part of prob and those are the only actions in plans
-/
lemma delete_relaxation_landmarks_are_landmarks {n : ℕ} (prob : PlanningTask n) (lm : List (Action n))
  (action_all_exist : lm.all (fun a => decide (a ∈ prob.actions)))
    (s : State' n) :
    is_delete_relaxed_disjunctive_action_landmark_for_state prob lm s →
      is_disjunctive_action_landmark_for_state prob (get_all_equiv_delete_relaxed_actions prob lm) s := by
        intro h
        refine' ⟨ _, _ ⟩
        · simp_all [ List.all_eq_true, get_all_equiv_delete_relaxed_actions ]
          exact fun x hx => Or.inr <| by simpa [ PlanningTask.actions ] using hx
        · intro plan
          have := delete_relaxation_landmarks_have_landmark_property prob lm s h plan
          obtain ⟨ a, ha₁, ha₂ ⟩ := this; use a; simp_all [ get_all_equiv_delete_relaxed_actions ]
          exact ⟨ by
            have h_mem : ∀ {s1 s2 : State n} {p : Path prob s1 s2}, ∀ a ∈ p.actionsUsed, a ∈ prob.actions' := by
              intros s1 s2 p a ha; induction p <;> simp_all [ Path.actionsUsed ]
              unfold PlanningTask.actions at *
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
lemma mem_get_all_equiv_iff {n : ℕ} (prob : PlanningTask n) (lm : List (Action n)) (a : Action n) :
    a ∈ get_all_equiv_delete_relaxed_actions prob lm ↔
      a ∈ prob.actions' ∧ ∃ l ∈ lm, delete_relax_action a = delete_relax_action l := by
  unfold get_all_equiv_delete_relaxed_actions
  simp [List.mem_filter, List.any_eq_true]

/-- Each action of the relax-equivalence closure is a genuine action of the problem. -/
lemma mem_actions_of_mem_get_all_equiv {n : ℕ} (prob : PlanningTask n) (lm : List (Action n))
    {a : Action n} (ha : a ∈ get_all_equiv_delete_relaxed_actions prob lm) : a ∈ prob.actions' :=
  ((mem_get_all_equiv_iff prob lm a).mp ha).1

/-- An action of the relax-equivalence closure shares the cost of one of the landmark's actions
(delete relaxation preserves costs). -/
lemma cost_eq_of_mem_get_all_equiv {n : ℕ} (prob : PlanningTask n) (lm : List (Action n))
    {a : Action n} (ha : a ∈ get_all_equiv_delete_relaxed_actions prob lm) :
    ∃ l ∈ lm, a.cost = l.cost := by
  obtain ⟨-, l, hl, he⟩ := (mem_get_all_equiv_iff prob lm a).mp ha
  exact ⟨l, hl, by have := congrArg Action.cost he; simpa [delete_relax_action] using this⟩

/-- A landmark action that is a genuine action of the problem belongs to its own
relax-equivalence closure. -/
lemma mem_get_all_equiv_of_mem {n : ℕ} (prob : PlanningTask n) (lm : List (Action n))
    {a : Action n} (ha : a ∈ lm) (ha' : a ∈ prob.actions') :
    a ∈ get_all_equiv_delete_relaxed_actions prob lm :=
  (mem_get_all_equiv_iff prob lm a).mpr ⟨ha', a, ha, rfl⟩

--- elementary landmark heuristic
def elementary_landmark_heuristic {n : ℕ} (prob : PlanningTask n) (lm : List (Action n))
    (s : State' n) : ℕ∞ :=
  if is_disjunctive_action_landmark_for_state prob lm s then
    if lm_empty : lm = [] then ⊤
    else
      let m : ℕ := (lm.map (fun a => a.cost)).min
        (by simp_all only [ne_eq, List.map_eq_nil_iff, not_false_eq_true])
      (m : ℕ∞)
  else 0

/-
Every action appearing in a `Path` is a member of the problem's action set.
-/
private lemma action_in_path_mem_actions {n : ℕ} {pt : PlanningTask n} {s s' : State n}
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
private lemma path_cost_ge_action_cost {n : ℕ} {pt : PlanningTask n} {s s' : State n}
    (p : Path pt s s') (a : Action n) (ha : a ∈ p.actionsUsed) : p.cost ≥ a.cost := by
  induction' p with a' s2 ha' succ p' ih generalizing a
  · cases ha
  · cases ha <;> simp_all [ Path.cost ]
    exact le_add_right ( by solve_by_elim )

lemma elementary_landmark_heuristic_is_admissible {n : ℕ} (prob : PlanningTask n)
    (lm : List (Action n)) :
    heur_admissible prob (elementary_landmark_heuristic prob lm) := by
  intro s plan
  by_cases h : is_disjunctive_action_landmark_for_state prob lm s
  · by_cases h' : lm = []
    · -- empty landmark: some action of `[]` occurs in the plan, impossible
      exfalso
      obtain ⟨a, ha, _⟩ := h.2 plan
      subst h'
      exact List.not_mem_nil ha
    · obtain ⟨ a, ha₁, ha₂ ⟩ := h.2 plan
      have hcost := path_cost_ge_action_cost plan.path a ha₂
      unfold elementary_landmark_heuristic
      rw [if_pos h, dif_neg h']
      simp only [Nat.cast_le]
      exact le_trans ( List.min_le_of_mem ( List.mem_map.mpr ⟨ a, ha₁, rfl ⟩ ) ) hcost
  · unfold elementary_landmark_heuristic
    rw [if_neg h]
    simp

/-- Every action appearing in a `Path` is a member of the problem's action set. -/
lemma mem_actions_of_mem_actionsUsed {n : ℕ} {pt : PlanningTask n} {s s' : State n}
    (p : Path pt s s') {a : Action n} (ha : a ∈ p.actionsUsed) : a ∈ pt.actions :=
  action_in_path_mem_actions p a ha

/-- The cost of a `Path` is the sum of the costs of the actions it uses. -/
lemma path_cost_eq_sum_actionsUsed {n : ℕ} {pt : PlanningTask n} {s s' : State n}
    (p : Path pt s s') : p.cost = (p.actionsUsed.map (fun a => a.cost)).sum := by
  induction p with
  | empty s => rfl
  | cons a s2 ha succ p' ih => simp [Path.cost, Path.actionsUsed, ih, Nat.add_comm]

end STRIPS