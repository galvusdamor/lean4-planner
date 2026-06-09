import planning.DeleteRelaxation
import planning.Planner


namespace Validator

instance STRIPS.actions.decidableMem {n : ℕ} (prob : STRIPS n) (a : Action n) :
Decidable (a ∈ prob.actions) := by sorry


-- should mean to test whether the action a is one of the action in the plan
instance STRIPS.plan.action.membership {n : ℕ} (prob : STRIPS n) (s : State n):  Membership (Action n) (Plan prob s) := by sorry


def is_disjunctive_action_landmark_for_state {n : ℕ} (prob : STRIPS n) (lm : List (Action n)) (s : State' n) : Prop := lm.all (fun a => decide (a ∈ prob.actions) ) ∧ (∀ plan : Plan prob (convertState s), ∃ a ∈ lm, a ∈ plan) 


-- remove all actions mentioned in lm
def remove_actions {n : ℕ} (prob : STRIPS n) (lm : List (Action n)) : STRIPS n :=
  let actions : Actions' n := prob.actions'.filter (fun a' => a' ∉ lm )
  STRIPS.mk prob.varNames actions prob.init' prob.goal'

def set_init {n : ℕ} (prob : STRIPS n) (s : State' n) : STRIPS n :=
  STRIPS.mk prob.varNames prob.actions' s prob.goal'


-- alternative characterisation of landmarks: if you remove the action, the problem must now be unsolvable
def action_set_removal_implies_unsolvable_for_state {n : ℕ} (prob : STRIPS n) (lm : List (Action n)) (s : State' n) : Prop := lm.all (fun a => decide (a ∈ prob.actions) ) ∧
  (Unsolvable (set_init (remove_actions prob lm) s)) 

lemma disjunctive_action_landmarks_iff_unsolvability {n : ℕ} (prob : STRIPS n) (lm : List (Action n)) (s : State' n):
    is_disjunctive_action_landmark_for_state prob lm s ↔ action_set_removal_implies_unsolvable_for_state prob lm s := by sorry


-- given that there is a planner and that planner is sound and complete (see Planner.lean), we can run the planne and look at its result to decide.
instance STRIPS.unsolvability.decidable {n : ℕ} (prob : STRIPS n) (lm : List (Action n))  : Decidable (Unsolvable prob) := by sorry


instance STRIPS.landmark.decidable {n : ℕ} (prob : STRIPS n) (lm : List (Action n)) (s : State' n) : Decidable (is_disjunctive_action_landmark_for_state prob lm s) := by sorry


-- delete relaxation landmark
def is_delete_relaxed_disjunctive_action_landmark_for_state {n : ℕ} (prob : STRIPS n) (lm : List (Action n)) (s : State' n) : Prop := lm.all (fun a => decide (a ∈ prob.actions) ) ∧ (∀ plan : Plan (delete_relaxation prob) (convertState s), ∃ a ∈ lm, a ∈ plan) 


lemma delete_relaxed_disjunctive_action_landmarks_iff_unsolvability_of_delete_relax {n : ℕ} (prob : STRIPS n) (lm : List (Action n)) (s : State' n):
    is_delete_relaxed_disjunctive_action_landmark_for_state prob lm s ↔
      action_set_removal_implies_unsolvable_for_state (delete_relaxation prob) lm s := by sorry


lemma delete_relaxation_landmarks_are_landmarks {n : ℕ} (prob : STRIPS n) (lm : List (Action n)) (s : State' n):
    is_delete_relaxed_disjunctive_action_landmark_for_state prob lm s → is_disjunctive_action_landmark_for_state prob lm s := by sorry




--- elementary landmark heuristic
def elementary_landmark_heuristic {n : ℕ} (prob : STRIPS n) (lm : List (Action n)) (s : State' n) : ℕ := if is_disjunctive_action_landmark_for_state prob lm s then
  if lm_empty : lm = [] then (2^n) * (max_action_cost prob)
  else
    (lm.map (fun a => a.cost)).min (by simp_all only [ne_eq, List.map_eq_nil_iff, not_false_eq_true])
  else 0


-- argument: if lm is not a landmark, nothing is to show.
-- if lm is a landmark and empty, the problem is unsolvable (all plans must contain an element of the empty set)
-- if lm is a landmark and non empty, every plan must contain one of its actions. The cost of it is ≤ cost of the plan. And the cost of the elementary_landmark_heuristic is ≤ the cost of that action in the plan as we take the minimum
lemma elementary_landmark_heuristic_is_admissible {n : ℕ} (prob : STRIPS n) (lm : List (Action n)) (s : State' n):
    heur_admissible prob (elementary_landmark_heuristic prob lm) := by sorry
