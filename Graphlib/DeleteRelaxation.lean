import Graphlib.Planner
-- h^+ calls the planner with h_zero on the delete relaxed task

namespace Validator

---------------- Delete relaxation heuristics

def delete_relax_action {n : ℕ} (a : Action n) : Action n := Action.mk a.name a.pre' a.add' ⟨[], by apply List.sortedLT_iff_pairwise.mpr ; simp ⟩  a.cost

def delete_relaxation {n : ℕ} (prob : STRIPS n) : STRIPS n := STRIPS.mk prob.varNames (prob.actions'.map delete_relax_action) prob.init' prob.goal'


/-- Corrected h_plus that solves the delete relaxation from state `s`.
Modified from the original: the planner now starts from `s` instead of always from
`prob.init'`, which is needed for admissibility over all starting states. -/
def h_plus {n : ℕ} (prob : STRIPS n) (s : State' n) : ℕ :=
  let del_relax_prob := STRIPS.mk prob.varNames (prob.actions'.map delete_relax_action) s prob.goal'
  let del_relax_ret := planner del_relax_prob (fun _ => 0)
  match del_relax_ret with
  | .none => (2^n) * (max_action_cost prob)
  | .some ret => ret.path.cost

/-- If preconditions are met in a state, they are also met in any state with more true bits. -/
private lemma satisfies'_mono {n : ℕ} (cond : VarSet' n) (s t : State' n)
    (h_sub : ∀ i : Fin n, s[i] → t[i])
    (h_sat : satisfies' cond s) :
    satisfies' cond t := by
  unfold satisfies' at *
  rw [List.all_eq_true] at *
  exact fun x hx => h_sub x (h_sat x hx)

-- The delete relaxation of a STRIPS problem with initial state v has a plan whose cost is
-- at most the cost of any path from v to a goal in the original problem's graph.

/-- delete_relax_action has empty delete effects. -/
private lemma delete_relax_action_del_empty {n : ℕ} (a : Action n) :
    (delete_relax_action a).del = ∅ := by
  unfold delete_relax_action Action.del convertVarSet
  simp

/-- The successor state under delete_relax_action a from s is s ∪ a.add. -/
private lemma del_relax_successor_eq {n : ℕ} (a : Action n) (s : State n) :
    Applicable s (delete_relax_action a) →
    Successor (delete_relax_action a) s (s ∪ (delete_relax_action a).add) := by
  intro h_app
  constructor
  · exact h_app
  · rw [delete_relax_action_del_empty]
    simp [Set.diff_empty]

/-- Given a walk in the original STRIPS graph and a state `s_del` whose true bits include
    those of the walk's starting vertex, we can build a STRIPS Path in the delete-relaxed
    problem from `convertState s_del` to some goal-satisfying state, with cost ≤ walk cost.
    The `del_prob` parameter is the delete-relaxed STRIPS problem (with arbitrary init'). -/
private lemma del_relax_path_from_walk {n : ℕ} (prob : STRIPS n)
    (del_prob : STRIPS n)
    (h_actions : del_prob.actions' = prob.actions'.map delete_relax_action)
    (_h_goal : del_prob.goal' = prob.goal')
    (v_orig goal : State' n)
    (v_del : State' n)
    (h_sub : ∀ i : Fin n, v_orig[i] → v_del[i])
    (walk : WeightedDiGraph.Walk (G := trans_of_STRIPS prob) v_orig goal)
    (h_goal_sat : satisfies' prob.goal' goal) :
    ∃ (last_del : State' n),
      (∀ i : Fin n, goal[i] → last_del[i]) ∧
      satisfies' prob.goal' last_del ∧
      ∃ (p : Path del_prob (convertState v_del) (convertState last_del)),
        p.cost ≤ walk.cost := by
  induction walk generalizing v_del with
  | nil =>
    -- Base case: v_orig = goal, so v_del already works
    exact ⟨v_del, h_sub, satisfies'_mono prob.goal' _ v_del h_sub h_goal_sat,
           Path.empty (convertState v_del), Nat.zero_le _⟩
  | @cons u w t adj rest ih =>
    -- There is an edge from u to w in the original graph
    have h_is_succ := is_successor_state_of_trans_STRIPS_adj prob u w adj
    -- Get the min_cost_action for this edge
    let a := min_cost_action prob u w h_is_succ
    have h_a_mem : a ∈ prob.actions' := min_cost_action_in_prob prob u w h_is_succ
    have h_a_app : applicable' a u = true := by unfold a min_cost_action; grind
    have h_a_succ : is_successor' a u w = true := by unfold a min_cost_action; grind
    -- delete_relax_action a is applicable to v_del (same preconditions, more true bits)
    have h_dr_app : satisfies' a.pre' v_del = true :=
      satisfies'_mono a.pre' u v_del h_sub h_a_app
    -- Compute the delete-relaxed successor state
    let w_del := successor' (delete_relax_action a) v_del
    -- w_del subsumes w: every true bit in w is also true in w_del
    have h_w_sub_w_del : ∀ i : Fin n, w[i] → w_del[i] := by
      intro i hi
      unfold w_del successor' delete_relax_action
      unfold is_successor' at h_a_succ
      simp only [List.all_eq_true, List.mem_finRange, true_implies] at h_a_succ
      specialize h_a_succ i
      split_ifs at h_a_succ ⊢ <;> simp_all [BitVec.getElem_ofBoolListLE]
    -- Apply IH
    obtain ⟨last_del, h_goal_sub, h_last_sat, p_rest, h_p_rest_cost⟩ := ih w_del h_w_sub_w_del h_goal_sat
    -- Successor relation for delete_relax_action a from v_del to w_del
    have h_dr_succ : Successor (delete_relax_action a) (convertState v_del) (convertState w_del) := by
      constructor
      · -- Applicable: a.pre ⊆ convertState v_del
        intro x hx
        show v_del[x]
        -- hx : x ∈ (delete_relax_action a).pre = convertVarSet a.pre' = a.pre'.val.toFinset
        have hx' : x ∈ a.pre'.val := by
          unfold Action.pre delete_relax_action convertVarSet at hx; simp at hx; exact hx
        exact List.all_eq_true.mp h_dr_app x hx'
      · -- convertState w_del = (convertState v_del \ del) ∪ add
        ext i
        unfold convertState w_del successor' delete_relax_action Action.del Action.add convertVarSet
        simp [BitVec.getElem_ofBoolListLE, Set.mem_union, Set.mem_setOf_eq]
        tauto
    -- Action membership in del_prob
    have h_dr_in_actions : delete_relax_action a ∈ del_prob.actions := by
      show delete_relax_action a ∈ List.toFinset del_prob.actions'
      rw [h_actions]; simp
      exact ⟨a, h_a_mem, rfl⟩
    -- Combine path
    refine ⟨last_del, h_goal_sub, h_last_sat,
      Path.cons (delete_relax_action a) (convertState w_del) h_dr_in_actions h_dr_succ p_rest, ?_⟩
    -- Cost bound
    show p_rest.cost + (delete_relax_action a).cost ≤ NatGraph.edgeCost adj + rest.cost
    calc p_rest.cost + (delete_relax_action a).cost
        = p_rest.cost + a.cost := rfl
      _ ≤ rest.cost + a.cost := Nat.add_le_add_right h_p_rest_cost _
      _ = rest.cost + cost_of prob u w h_is_succ := by
            rw [min_cost_action_cost_eq_cost_of prob u w h_is_succ]
      _ = rest.cost + NatGraph.edgeCost adj := by
            rw [trans_of_STRIPS_edgeCost prob u w adj]
      _ = NatGraph.edgeCost adj + rest.cost := Nat.add_comm _ _

private lemma del_relax_plan_exists_from_path {n : ℕ} (prob : STRIPS n) (v goal : State' n)
    (goal_in_goals : goal ∈ trans_of_STRIPS_goals prob)
    (path : (trans_of_STRIPS prob).Path v goal) :
    ∃ plan : Plan (STRIPS.mk prob.varNames (prob.actions'.map delete_relax_action) v prob.goal')
        (convertState v), plan.path.cost ≤ path.cost := by
  -- goal satisfies the goal condition
  have h_goal_sat : satisfies' prob.goal' goal := by
    exact ((mem_trans_of_STRIPS_goals_iff prob goal).mp goal_in_goals)
  -- Use del_relax_path_from_walk with v_del = v and identity subsumption
  set dp := STRIPS.mk prob.varNames (prob.actions'.map delete_relax_action) v prob.goal'
  obtain ⟨last_del, _, h_last_sat, p, h_p_cost⟩ :=
    del_relax_path_from_walk prob dp rfl rfl v goal v (fun _ h => h) path.val h_goal_sat
  -- Build a plan
  have h_goal_state : (STRIPS.mk prob.varNames (prob.actions'.map delete_relax_action) v prob.goal').GoalState (convertState last_del) := by
    exact satisfies'_implies_GoalState (STRIPS.mk prob.varNames (prob.actions'.map delete_relax_action) v prob.goal') last_del h_last_sat
  refine ⟨⟨convertState last_del, p, h_goal_state⟩, ?_⟩
  calc p.cost ≤ path.val.cost := h_p_cost
    _ = path.cost := (WeightedDiGraph.Path.cost_same path).symm

lemma h_plus_admissible {n : ℕ} (prob : STRIPS n) : heur_admissible' prob (h_plus prob) := by
  intro v goal goal_in_goals path
  unfold h_plus
  simp only
  split
  case h_1 h_none =>
    -- Planner returned none: h_plus = 2^n * max_action_cost
    -- But we have a path from v to goal, so del_relax_plan_exists_from_path gives a plan
    have ⟨plan, _⟩ := del_relax_plan_exists_from_path prob v goal goal_in_goals path
    -- But planner returned none means unsolvable - contradiction
    have unsolvable := planner_complete _ _ h_none
    have : STRIPS.init (STRIPS.mk prob.varNames (prob.actions'.map delete_relax_action) v prob.goal') = convertState v := rfl
    rw [show Unsolvable _ = IsEmpty (Plan _ (convertState v)) from by unfold Unsolvable UnsolvableState STRIPS.init; rfl] at unsolvable
    exact False.elim (unsolvable.false plan)
  case h_2 ret h_some =>
    -- Planner returned some plan: h_plus = ret.path.cost
    obtain ⟨del_plan, h_del_plan_cost⟩ := del_relax_plan_exists_from_path prob v goal goal_in_goals path
    -- abbreviation for the delete-relaxed problem
    let dp := STRIPS.mk prob.varNames (prob.actions'.map delete_relax_action) v prob.goal'
    have h_isSome : (planner dp (fun _ => 0)).isSome := by
      show (planner _ _).isSome; rw [h_some]; simp
    have h_opt := planner_optimal dp (fun _ => 0) (zero_heur_admissible _) h_isSome
    specialize h_opt del_plan
    have h_get_eq : (planner dp (fun _ => 0)).get h_isSome = ret := by
      show (planner _ _).get _ = _
      exact Option.get_of_eq_some (by show (planner _ _).isSome; rw [h_some]; simp) h_some
    rw [h_get_eq] at h_opt
    exact le_trans h_opt h_del_plan_cost
