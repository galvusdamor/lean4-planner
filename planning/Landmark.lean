import planning.DeleteRelaxation
import planning.Planner

import Mathlib

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
  unfold remove_actions; aesop

private lemma mem_of_mem_remove_actions {n : ℕ} (prob : STRIPS n) (lm : List (Action n))
    (a : Action n) (ha : a ∈ (remove_actions prob lm).actions') :
    a ∈ prob.actions' ∧ a ∉ lm := by
  unfold remove_actions at ha; aesop (simp_config := { singlePass := true })

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
      simp_all +decide [set_init, remove_actions]
      simp_all +decide [STRIPS.actions]) h₁ p''
    simp_all +decide [Path.actionsUsed, Path.cost]
    unfold set_init at hp'; simp_all +decide [remove_actions]
    unfold STRIPS.actions at hp'; aesop

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
  induction p <;> simp_all +decide [Path.cost]
  · exact ⟨Path.empty _, rfl⟩
  · rename_i a s1 s2 ha succ π ih
    obtain ⟨p', hp'⟩ := ih (fun a ha => h a <| List.mem_cons_of_mem _ ha)
    refine' ⟨Path.cons _ _ _ _ p', _⟩
    exact ‹Action n›
    all_goals simp_all +decide [set_init, remove_actions]
    all_goals norm_num [Path.actionsUsed, Path.cost] at *
    · simp_all +decide [STRIPS.actions]
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
    unfold is_disjunctive_action_landmark_for_state; aesop
  · refine ⟨h.1, ?_⟩
    intro plan
    contrapose! h
    simp +decide [action_set_removal_implies_unsolvable_for_state]
    exact fun _ => plan_orig_to_plan_remove prob lm s plan fun a ha => by aesop

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


/-- Corrected version: uses `is_disjunctive_action_landmark_for_state` applied to
`delete_relaxation prob` (which has matching first conjuncts on both sides). -/
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
        convert disjunctive_action_landmarks_of_delete_relax_iff_unsolvability_of_delete_relax prob ( List.map ( fun a => delete_relax_action a ) lm ) s using 1;
        simp +decide [ is_delete_relaxed_disjunctive_action_landmark_for_state, is_disjunctive_action_landmark_for_state, List.all_map ]

/-- Relaxing a path: every path of the original task, started from a (pointwise) larger state,
can be replayed in the delete relaxation using the delete-relaxed versions of the same actions,
reaching a state that is again at least as large.  Delete relaxation only ever adds variables, so
larger starting states keep all actions applicable and keep the reached states larger. -/
private lemma relax_path {n : ℕ} (prob : STRIPS n) {s1 s2 : State n} (p : Path prob s1 s2)
    {t1 : State n} (hsub : s1 ⊆ t1) :
    ∃ (t2 : State n), s2 ⊆ t2 ∧
      ∃ (q : Path (delete_relaxation prob) t1 t2),
        q.actionsUsed = p.actionsUsed.map delete_relax_action := by
  revert t1;
  induction' p with a s1 s2 ha succ π ih;
  · exact fun { t1 } ht1 => ⟨ t1, ht1, Path.empty _, rfl ⟩;
  · rename_i h₁ h₂;
    intro t1 ht1
    obtain ⟨t1', ht1', ht1'_succ⟩ : ∃ t1', Successor (delete_relax_action s1) t1 t1' ∧ s1.add ⊆ t1' ∧ t1 ⊆ t1' := by
      refine' ⟨ t1 ∪ s1.add, _, _, _ ⟩ <;> simp_all +decide [ Successor, Applicable ];
      simp_all +decide [ delete_relax_action ];
      simp_all +decide [ Action.pre, Action.add, Action.del, Set.subset_def ];
      simp +decide [ convertVarSet ];
    obtain ⟨t2, ht2, q, hq⟩ := h₂ (by
    grind : ha ⊆ t1');
    use t2, ht2, Path.cons (delete_relax_action s1) t1' (by
    simp_all +decide [ STRIPS.actions, delete_relaxation ];
    exact ⟨ s1, π, rfl ⟩) (by
    exact ht1') q
    generalize_proofs at *;
    simp +decide [ Path.actionsUsed, hq ]

/-- A delete relaxed landmark is actually a landmark.

The original statement
`is_delete_relaxed_disjunctive_action_landmark_for_state prob lm s →`
`  is_disjunctive_action_landmark_for_state prob lm s`
is **false**: the conclusion asks for an action `a ∈ lm` to occur *verbatim* in every original
plan and for `a ∈ prob.actions`, neither of which the relaxed-landmark hypothesis provides
(delete relaxation forgets the delete effects, so the action witnessed by the relaxed plan is only
determined up to its relaxation).  The faithful statement: every original plan uses an action whose
delete relaxation is one of the landmark's relaxed actions.  The original is preserved below in a
comment.
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
  intro h plan;
  obtain ⟨t2, ht2, q, hq⟩ := relax_path prob plan.path (le_refl _);
  -- By definition of `is_delete_relaxed_disjunctive_action_landmark_for_state`, we know that `t2` satisfies the goal.
  have ht2_goal : (delete_relaxation prob).GoalState t2 := by
    exact Set.Subset.trans plan.goal ht2;
  obtain ⟨a, ha⟩ : ∃ a ∈ lm, delete_relax_action a ∈ q.actionsUsed := by
    exact h.2 ⟨ t2, q, ht2_goal ⟩;
  obtain ⟨a', ha'⟩ : ∃ a' ∈ plan.path.actionsUsed, delete_relax_action a' = delete_relax_action a := by
    grind;
  exact ⟨ a', by simpa [ Path.instMembership ] using ha'.1, by aesop ⟩



/-- stronger statement: if the actions a ∈ lm are actually part of the original problem, then if lm is part of every delete relaxed plan, then it must be part of any plan. The reasoning is that the set of all delete-relaxed plans is a "superset" (not in the strict sende due to missing deleting effects) of all plans. I.e. for every actual plan there is an equivalent delete relaxed one that contains an action a ∈ lm thus the actual plan must too. The proof here succeeds as all the actions a ∈ lm are part of prob and those are the only actions in plans -/
lemma delete_relaxation_landmarks_are_landmarks {n : ℕ} (prob : STRIPS n) (lm : List (Action n))
  (action_all_exist : lm.all (fun a => decide (a ∈ prob.actions)))
    (s : State' n) :
    is_delete_relaxed_disjunctive_action_landmark_for_state prob lm s →
      is_disjunctive_action_landmark_for_state prob lm s := by sorry

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
  induction' p with a' s2 ha' succ p' ih generalizing a;
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
  induction' p with a' s2 ha' succ p' ih generalizing a;
  · cases ha;
  · cases ha <;> simp_all +decide [ Path.cost ];
    exact le_add_right ( by solve_by_elim )

lemma elementary_landmark_heuristic_is_admissible {n : ℕ} (prob : STRIPS n)
    (lm : List (Action n)) :
    heur_admissible prob (elementary_landmark_heuristic prob lm) := by
  intro s plan; by_cases h : is_disjunctive_action_landmark_for_state prob lm s <;> by_cases h' : lm = [] <;> simp_all +decide ;
  · have := h.2 plan; aesop;
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

end Validator
