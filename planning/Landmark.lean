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
  lm.all (fun a => decide (a ∈ prob.actions)) ∧
    (∀ plan : Plan (delete_relaxation prob) (convertState s), ∃ a ∈ lm, a ∈ plan)

/-
The lemma below is false as stated because `is_delete_relaxed_disjunctive_action_landmark_for_state`
checks `a ∈ prob.actions` in its first conjunct, while `action_set_removal_implies_unsolvable_for_state
(delete_relaxation prob)` checks `a ∈ (delete_relaxation prob).actions`. These differ: the former is
`prob.actions'.toFinset` while the latter is `(prob.actions'.map delete_relax_action).toFinset`.

Counterexample: n = 1, prob with one action `a` having non-empty `del'`, an unsolvable initial
state, and `lm = [a]`. Then `a ∈ prob.actions` is true and the ∀-over-plans is vacuously true
(no plans exist for the unsolvable delete-relaxed problem), so the LHS is true.
But `a ∉ (delete_relaxation prob).actions` since `delete_relax_action a ≠ a`, so the RHS
first conjunct fails, making it false.
-/
/- lemma delete_relaxed_disjunctive_action_landmarks_iff_unsolvability_of_delete_relax
    {n : ℕ} (prob : STRIPS n) (lm : List (Action n)) (s : State' n):
    is_delete_relaxed_disjunctive_action_landmark_for_state prob lm s ↔
      action_set_removal_implies_unsolvable_for_state (delete_relaxation prob) lm s := by
  sorry -/

/-- Corrected version: uses `is_disjunctive_action_landmark_for_state` applied to
`delete_relaxation prob` (which has matching first conjuncts on both sides). -/
lemma disjunctive_action_landmarks_iff_unsolvability_of_delete_relax {n : ℕ} (prob : STRIPS n)
    (lm : List (Action n)) (s : State' n) :
    is_disjunctive_action_landmark_for_state (delete_relaxation prob) lm s ↔
      action_set_removal_implies_unsolvable_for_state (delete_relaxation prob) lm s :=
  disjunctive_action_landmarks_iff_unsolvability (delete_relaxation prob) lm s

/-
The lemma below is false as stated because `is_delete_relaxed_disjunctive_action_landmark_for_state`
checks `a ∈ prob.actions` in the first conjunct, but the plans are for `delete_relaxation prob`,
whose actions are `delete_relax_action` images. When `lm` contains an action `a` with non-empty
`del'`, `a` cannot appear in any delete-relaxed plan (since those use `delete_relax_action`
versions), and its delete-relaxed counterpart `delete_relax_action a` may have a "twin" in the
original problem's action list with different `del'`.


Counterexample: n = 2, init = {0=F, 1=T}, goal = {0}. Actions:
  a (name="a", pre=∅, add={0}, del=∅, cost=1),
  b (name="a", pre=∅, add={0}, del={1}, cost=1).
With lm = [a]: delete_relax_action b = a since they share name/pre/add/cost and
delete_relax_action sets del=∅. So every plan for delete_relaxation prob uses action `a`.
But the original plan [b] (apply b: {0=T,1=F}, goal {0} satisfied) does not use `a`.
-/
/- lemma delete_relaxation_landmarks_are_landmarks {n : ℕ} (prob : STRIPS n) (lm : List (Action n))
    (s : State' n):
    is_delete_relaxed_disjunctive_action_landmark_for_state prob lm s →
      is_disjunctive_action_landmark_for_state prob lm s := by
  sorry -/


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
