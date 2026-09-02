import planning.Planner

-- h^+ calls the planner with h_zero on the delete relaxed task

namespace STRIPS

---------------- Delete relaxation heuristics

def delete_relax_action {n : ℕ} (a : Action n) : Action n := Action.mk a.name a.pre a.add (∅ : VarSet n) a.cost

def delete_relaxation {n : ℕ} (prob : PlanningTask n) : PlanningTask n := PlanningTask.mk prob.varNames (prob.actions'.map delete_relax_action) prob.init' prob.goal'


/-- Corrected h_plus that solves the delete relaxation from state `s`.
Modified from the original: the planner now starts from `s` instead of always from
`prob.init'`, which is needed for admissibility over all starting states. -/
def h_plus {n : ℕ} (prob : PlanningTask n) (s : BitVec n) : ℕ∞ :=
  let del_relax_prob := PlanningTask.mk prob.varNames (prob.actions'.map delete_relax_action) (varset'_of_state' s) prob.goal'
  let del_relax_ret := planner del_relax_prob (fun _ => 0)
  match del_relax_ret with
  | .none => ⊤
  | .some ret => (ret.path.cost : ℕ∞)

/-- If preconditions are met in a state, they are also met in any state with more true bits. -/
private lemma satisfies'_mono {n : ℕ} (cond : VarSet n) (s t : BitVec n)
    (h_sub : ∀ i : Fin n, s[i] → t[i])
    (h_sat : satisfies' cond s) :
    satisfies' cond t := by
  rw [satisfies'_iff] at *
  exact fun x hx => h_sub x (h_sat x hx)

-- The delete relaxation of a STRIPS problem with initial state v has a plan whose cost is
-- at most the cost of any path from v to a goal in the original problem's graph.

/-- delete_relax_action has empty delete effects. -/
private lemma delete_relax_action_del_empty {n : ℕ} (a : Action n) :
    (delete_relax_action a).del = ∅ := by simp [delete_relax_action]

/-
The successor state under delete_relax_action a from s is s ∪ a.add.
-/
private lemma del_relax_successor_eq {n : ℕ} (a : Action n) (s : State n) :
    Applicable s (delete_relax_action a) →
    Successor (delete_relax_action a) s (s ∪ (delete_relax_action a).add) := by
  intro h;
  constructor;
  · assumption;
  · simp +decide [ delete_relax_action ]

/-- Transfer a path between two planning tasks that have the same action list (paths only depend
on the actions, not on the initial state or variable names), preserving the cost. -/
private lemma dr_path_transfer_of_actions_eq {n : ℕ} (pt1 pt2 : PlanningTask n)
    (h : pt1.actions' = pt2.actions') {s1 s2 : State n} (p : PlanningTask.Path pt1 s1 s2) :
    ∃ q : PlanningTask.Path pt2 s1 s2, q.cost = p.cost := by
  induction p with
  | empty t => exact ⟨PlanningTask.Path.empty t, rfl⟩
  | cons a s2 ha succ p ih =>
    obtain ⟨q, hq⟩ := ih
    have hmem : a ∈ pt2.actions := by
      simp only [PlanningTask.actions, ← h]; exact ha
    exact ⟨PlanningTask.Path.cons a s2 hmem succ q, by simp [PlanningTask.Path.cost, hq]⟩

/-- A STRIPS path relaxes to a delete-relaxed path from any larger start state: the reachable
state only grows, applicability is preserved, and the cost is unchanged (delete relaxation only
drops delete effects, keeping costs). -/
private lemma dr_relax_path {n : ℕ} (prob : PlanningTask n) {s1 s2 : State n}
    (p : PlanningTask.Path prob s1 s2) {t1 : State n} (hsub : s1 ⊆ t1) :
    ∃ (t2 : State n), s2 ⊆ t2 ∧
      ∃ (q : PlanningTask.Path (delete_relaxation prob) t1 t2), q.cost = p.cost := by
  induction p generalizing t1 with
  | empty t => exact ⟨t1, hsub, PlanningTask.Path.empty t1, rfl⟩
  | cons a s_mid ha succ π ih =>
    -- `a` is applicable in `s1` (its preconditions hold), hence also in the larger `t1`.
    obtain ⟨happ, hsucc⟩ := succ
    have happ_t1 : Applicable t1 a := happ.trans hsub
    -- Applying the delete-relaxed action to `t1` yields `t1 ∪ a.add`, which still dominates `s_mid`.
    have hmid_sub : s_mid ⊆ t1 ∪ a.add := by
      rw [hsucc]
      intro i hi
      rcases hi with ⟨hi, _⟩ | hi
      · exact Or.inl (hsub hi)
      · exact Or.inr hi
    obtain ⟨t2, ht2, q, hq⟩ := ih hmid_sub
    have hmem : delete_relax_action a ∈ (delete_relaxation prob).actions := by
      simp only [PlanningTask.actions, Finset.mem_coe, List.mem_toFinset, delete_relaxation]
      exact List.mem_map_of_mem (mem_actions'_of_mem_actions ha)
    have hsucc' : Successor (delete_relax_action a) t1 (t1 ∪ a.add) := by
      have := del_relax_successor_eq a t1 happ_t1
      simpa [delete_relax_action, Action.add] using this
    exact ⟨t2, ht2, PlanningTask.Path.cons (delete_relax_action a) (t1 ∪ a.add) hmem hsucc' q, by
      simp [PlanningTask.Path.cost, delete_relax_action, hq]⟩

/-- Given a walk in the original STRIPS graph and a state `s_del` whose true bits include
    those of the walk's starting vertex, we can build a STRIPS PlanningTask.Path in the delete-relaxed
    problem from `convertState s_del` to some goal-satisfying state, with cost ≤ walk cost.
    The `del_prob` parameter is the delete-relaxed STRIPS problem (with arbitrary init'). -/
private lemma del_relax_path_from_walk {n : ℕ} (prob : PlanningTask n)
    (del_prob : PlanningTask n)
    (h_actions : del_prob.actions' = prob.actions'.map delete_relax_action)
    (_h_goal : del_prob.goal' = prob.goal')
    (v_orig goal : BitVec n)
    (v_del : BitVec n)
    (h_sub : ∀ i : Fin n, v_orig[i] → v_del[i])
    (walk : WeightedDiGraph.Walk (G := trans_of_STRIPS prob) v_orig goal)
    (h_goal_sat : satisfies' prob.goal' goal) :
    ∃ (last_del : BitVec n),
      (∀ i : Fin n, goal[i] → last_del[i]) ∧
      satisfies' prob.goal' last_del ∧
      ∃ (p : PlanningTask.Path del_prob (convertState v_del) (convertState last_del)),
        p.cost ≤ walk.cost := by
  classical
  -- Turn the graph walk into a STRIPS path of the original problem.
  have hsub' : (convertState v_orig : State n) ⊆ convertState v_del := by
    intro i hi
    rw [mem_convertState] at hi ⊢
    exact h_sub i hi
  -- Relax it to a delete-relaxed path from the larger start `convertState v_del`.
  obtain ⟨t2, ht2, q, hq⟩ :=
    dr_relax_path prob (walk_to_strips_path prob walk h_goal_sat) hsub'
  obtain ⟨last_del, hlast⟩ := state_has_bitvec t2
  subst hlast
  -- Move the path into `del_prob` (same actions).
  obtain ⟨q', hq'⟩ := dr_path_transfer_of_actions_eq (delete_relaxation prob) del_prob
    (by rw [h_actions]; rfl) q
  refine ⟨last_del, ?_, ?_, q', ?_⟩
  · intro i hgi
    have hmem : i ∈ convertState last_del := ht2 (mem_convertState.mpr hgi)
    rwa [mem_convertState] at hmem
  · have hg1 : prob.GoalState (convertState goal) :=
      satisfies'_implies_GoalState prob goal h_goal_sat
    exact GoalState_implies_satisfies' prob last_del (hg1.trans ht2)
  · rw [hq', hq]
    exact le_of_eq (walk_to_strips_path_cost_eq prob walk h_goal_sat)

private lemma del_relax_plan_exists_from_path {n : ℕ} (prob : PlanningTask n) (v goal : BitVec n)
    (goal_in_goals : goal ∈ trans_of_STRIPS_goals prob)
    (path : (trans_of_STRIPS prob).Path v goal) :
    ∃ plan : PlanningTask.Plan (PlanningTask.mk prob.varNames (prob.actions'.map delete_relax_action) (varset'_of_state' v) prob.goal')
        (convertState v), plan.path.cost ≤ path.cost := by
  -- goal satisfies the goal condition
  have h_goal_sat : satisfies' prob.goal' goal := by
    exact ((mem_trans_of_STRIPS_goals_iff prob goal).mp goal_in_goals)
  -- Use del_relax_path_from_walk with v_del = v and identity subsumption
  set dp := PlanningTask.mk prob.varNames (prob.actions'.map delete_relax_action) (varset'_of_state' v) prob.goal'
  obtain ⟨last_del, _, h_last_sat, p, h_p_cost⟩ :=
    del_relax_path_from_walk prob dp rfl rfl v goal v (fun _ h => h) path.val h_goal_sat
  -- Build a plan
  have h_goal_state : (PlanningTask.mk prob.varNames (prob.actions'.map delete_relax_action) (varset'_of_state' v) prob.goal').GoalState (convertState last_del) := by
    exact satisfies'_implies_GoalState (PlanningTask.mk prob.varNames (prob.actions'.map delete_relax_action) (varset'_of_state' v) prob.goal') last_del h_last_sat
  refine ⟨⟨convertState last_del, p, h_goal_state⟩, ?_⟩
  calc p.cost ≤ path.val.cost := h_p_cost
    _ = path.cost := (WeightedDiGraph.Path.cost_same path).symm

lemma h_plus_admissible {n : ℕ} (prob : PlanningTask n) : heur_admissible' prob (h_plus prob) := by
  intro v goal goal_in_goals path
  unfold h_plus
  simp only
  split
  case h_1 h_none =>
    -- Planner returned none: h_plus = ⊤
    -- But we have a path from v to goal, so del_relax_plan_exists_from_path gives a plan
    have ⟨plan, _⟩ := del_relax_plan_exists_from_path prob v goal goal_in_goals path
    -- But planner returned none means unsolvable - contradiction
    have unsolvable := planner_complete _ _ (zero_heur_admissible' _) h_none
    have hinit : PlanningTask.init (PlanningTask.mk prob.varNames
        (prob.actions'.map delete_relax_action) (varset'_of_state' v) prob.goal') = convertState v := by
      ext i
      simp [PlanningTask.init, convertState, varset'_of_state', VarSet.mem_iff]
    rw [show PlanningTask.Unsolvable _ = IsEmpty (PlanningTask.Plan _ (convertState v)) from by
      unfold PlanningTask.Unsolvable PlanningTask.UnsolvableState
      rw [hinit]] at unsolvable
    exact False.elim (unsolvable.false plan)
  case h_2 ret h_some =>
    -- Planner returned some plan: h_plus = ret.path.cost
    obtain ⟨del_plan, h_del_plan_cost⟩ := del_relax_plan_exists_from_path prob v goal goal_in_goals path
    -- abbreviation for the delete-relaxed problem
    let dp := PlanningTask.mk prob.varNames (prob.actions'.map delete_relax_action) (varset'_of_state' v) prob.goal'
    have h_isSome : (planner dp (fun _ => 0)).isSome := by
      show (planner _ _).isSome; rw [h_some]; simp
    have h_opt := planner_optimal dp (fun _ => 0) (zero_heur_admissible _) h_isSome
    have hdpinit : dp.init = convertState v := by
      ext i
      simp [dp, PlanningTask.init, convertState, varset'_of_state', VarSet.mem_iff]
    let del_plan' : PlanningTask.Plan dp dp.init := hdpinit.symm ▸ del_plan
    specialize h_opt del_plan'
    have h_get_eq : (planner dp (fun _ => 0)).get h_isSome = ret := by
      show (planner _ _).get _ = _
      exact Option.get_of_eq_some (by show (planner _ _).isSome; rw [h_some]; simp) h_some
    rw [h_get_eq] at h_opt
    have transport_plan_cost {s t : State n} (h : s = t) (pl : PlanningTask.Plan dp t) :
        (h.symm ▸ pl).path.cost = pl.path.cost := by
      cases h
      rfl
    have hpathcost : del_plan'.path.cost = del_plan.path.cost := by
      change (hdpinit.symm ▸ del_plan).path.cost = del_plan.path.cost
      exact transport_plan_cost hdpinit del_plan
    have hcost' : del_plan'.path.cost ≤ path.cost := hpathcost ▸ h_del_plan_cost
    exact_mod_cast le_trans h_opt hcost'
