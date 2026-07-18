import SearchAlgorithms.AStar
import planning.Heuristics
import planning.SearchCompat

namespace STRIPS

/-- The STRIPS admissibility predicate `heur_admissible'` is *definitionally* the
`SearchAlgorithms` graph admissibility predicate `admissible'` for the transition graph
`trans_of_STRIPS prob` with goal list `trans_of_STRIPS_goals prob`. -/
lemma admissible'_of_heur_admissible' {n : ℕ} (prob : PlanningTask n) (heur : State' n → ℕ∞)
    (h : heur_admissible' prob heur) :
    (trans_of_STRIPS prob).admissible' heur (trans_of_STRIPS_goals prob) := h

/-- An admissible heuristic is finite (`≠ ⊤`) at every vertex of a path that ends in a goal:
each such vertex admits a (suffix) path to the goal, whose finite cost bounds the heuristic. -/
lemma heur_ne_top_on_path {n : ℕ} (prob : PlanningTask n) (heur : State' n → ℕ∞)
    (admissible : heur_admissible' prob heur)
    {goal : State' n} (goal_in_goals : goal ∈ trans_of_STRIPS_goals prob)
    (p : (trans_of_STRIPS prob).Path prob.init' goal) :
    ∀ u ∈ p.support, heur u ≠ ⊤ := by
  intro u hu
  -- The suffix of `p` starting at `u` is a walk from `u` to `goal`.
  obtain ⟨p', _⟩ := WeightedDiGraph.Walk.cheaper_path_exists (p.val.dropUntil u hu)
  have hle := admissible u goal goal_in_goals p'
  exact ne_top_of_le_ne_top (by simp) hle


def planner {n : ℕ} (prob : PlanningTask n) (heur : State' n → ℕ∞): Option (Plan prob prob.init) :=
  let trans := trans_of_STRIPS prob
  let ini := prob.init'
  let goals := trans_of_STRIPS_goals prob

  let opt_ret := NatGraph.astar_multigoal (g:=trans) heur ini goals
  match opt_ret with
  | .none => .none
  | .some ret =>
    let goal' : State' n := ret.1
    have goal'_in_goals : goal' ∈ goals := by apply ret.1.prop

    have sat : satisfies' prob.goal' goal' := by
      unfold goals at goal'_in_goals
      simp [trans_of_STRIPS_goals] at goal'_in_goals
      exact (satisfies'_iff prob.goal' goal').mpr goal'_in_goals.2

    let path : Path prob (convertState ini) (convertState goal') := walk_to_strips_path prob ret.2.val sat
    have goal_sat : prob.GoalState (convertState goal') :=
      satisfies'_implies_GoalState prob goal' sat
    let plan : Plan prob prob.init := Plan.mk (convertState ret.fst) path goal_sat
    Option.some plan

/--admissibility not needed: we only needed that the heuristic is not discarding solvable states -/
lemma planner_complete {n : ℕ} (prob : PlanningTask n) (heur : State' n → ℕ∞)
      (admissible : heur_admissible' prob heur):
      planner prob heur = Option.none → Unsolvable prob := by
  intro ret_none
  unfold Unsolvable UnsolvableState
  constructor
  intro plan
  let plan_path : Path prob prob.init plan.last := plan.path
  unfold PlanningTask.init at plan_path
  have last_dec : DecidablePred (Set.Mem plan.last) := last_dec prob prob.init' plan.last plan_path
  obtain ⟨goal',goal_eq_goal'⟩ := state_has_bitvec plan.last
  rw [←goal_eq_goal'] at plan_path
  let walk := strips_path_to_walk prob plan_path


  unfold planner at ret_none
  simp at ret_none
  split at ret_none
  · expose_names
    have goal'_in_goals : goal' ∈ trans_of_STRIPS_goals prob := by
      have gs := plan.goal
      rw [← goal_eq_goal'] at gs
      have hsat := GoalState_implies_satisfies' prob goal' gs
      exact (mem_trans_of_STRIPS_goals_iff prob goal').mpr hsat
    obtain ⟨path,_⟩ := walk.shorter_path_exists
    have h_complete := NatGraph.astar_multigoal_is_complete heur prob.init'
      (trans_of_STRIPS_goals prob)
      ⟨goal', goal'_in_goals, path, heur_ne_top_on_path prob heur admissible goal'_in_goals path⟩
    rw [heq] at h_complete
    simp at h_complete
  · grind -- some = none




/-- The A* multigoal result is optimal across all goals: its graph path cost is ≤ any graph path
    to any goal in the goals list. -/
lemma astar_multigoal_cross_goal_optimal {n : ℕ} (prob : PlanningTask n) (heur : State' n → ℕ∞)
    (goals : List (State' n))
    (admissible : (trans_of_STRIPS prob).admissible' heur goals)
    (returned_path : Option.isSome (NatGraph.astar_multigoal (g := trans_of_STRIPS prob)
      heur prob.init' goals)) :
    ∀ goal ∈ goals, ∀ p : (trans_of_STRIPS prob).Path prob.init' goal,
      ((NatGraph.astar_multigoal (g := trans_of_STRIPS prob)
        heur prob.init' goals).get returned_path).2.cost ≤ p.cost := by
  intro goal goal_in_goals p
  -- Extract augmented A* path
  have h_some : ∃ aug_path, NatGraph.astar
      (g := (trans_of_STRIPS prob).add_artificial_goal (· ∈ goals))
      (NatGraph.opt_heur heur) (some prob.init') none = some aug_path := by
    exact Option.isSome_iff_exists.mp
      (NatGraph.astar_multigoal_some_implies_astar_some heur prob.init' goals returned_path)
  obtain ⟨aug_path, h_eq⟩ := h_some
  -- The augmented path is optimal
  have aug_optimal : aug_path.is_cheapest := by
    have aug_ret : Option.isSome (NatGraph.astar
        (g := (trans_of_STRIPS prob).add_artificial_goal (· ∈ goals))
        (NatGraph.opt_heur heur) (some prob.init') none) := by
      rw [h_eq]; simp
    have h := NatGraph.astar_is_optimal
      (g := (trans_of_STRIPS prob).add_artificial_goal (· ∈ goals))
      (NatGraph.opt_heur heur) (some prob.init') none
      (NatGraph.opt_heur_admissible heur admissible) aug_ret
    have h_get : (NatGraph.astar
        (g := (trans_of_STRIPS prob).add_artificial_goal (· ∈ goals))
        (NatGraph.opt_heur heur) (some prob.init') none).get aug_ret = aug_path := by
      simp [h_eq]
    rw [h_get] at h
    exact h
  -- Lift p to augmented path
  obtain ⟨aug_p, h_cost_eq⟩ := NatGraph.lift_path_to_augmented_cost
    (G := trans_of_STRIPS prob) (is_goal := (· ∈ goals)) goal_in_goals p
  -- Chain: returned.cost ≤ aug_path.cost ≤ aug_p.cost = p.cost
  have h1 : aug_path.cost ≤ p.cost := calc
    aug_path.cost ≤ aug_p.cost := aug_optimal aug_p
    _ = p.cost := h_cost_eq
  have h2 := NatGraph.astar_multigoal_cost_le_aug
    heur prob.init' goals returned_path aug_path h_eq
  exact le_trans h2 h1

/-- When planner returns some, the underlying A* also returns some. -/
lemma planner_isSome_implies_astar_isSome {n : ℕ} (prob : PlanningTask n) (heur : State' n → ℕ∞)
    (ret_plan : (planner prob heur).isSome) :
    Option.isSome (NatGraph.astar_multigoal (g := trans_of_STRIPS prob)
      heur prob.init'
      ((List.finRange (2^n)).filter (fun s => satisfies' prob.goal' s))) := by
  -- By definition of planner, if the planner returns some, then the astar_multigoal must have returned some.
  unfold planner at ret_plan
  simp_all only [BitVec.natCast_eq_ofNat, List.pure_def, List.bind_eq_flatMap]
  split at ret_plan
  next opt_ret heq => simp_all only [Option.isSome_none, Bool.false_eq_true]
  next opt_ret ret heq => simp_all only [Option.isSome_some, trans_of_STRIPS_goals,BitVec.natCast_eq_ofNat, List.pure_def, List.bind_eq_flatMap, Option.isSome_some]

/-- The planner's path cost equals the A* multigoal result's graph path cost. -/
lemma planner_path_cost_eq_astar {n : ℕ} (prob : PlanningTask n) (heur : State' n → ℕ∞)
    (ret_plan : (planner prob heur).isSome) :
    ((planner prob heur).get ret_plan).path.cost =
      ((NatGraph.astar_multigoal (g := trans_of_STRIPS prob) heur prob.init'
        ((List.finRange (2^n)).filter (fun s => satisfies' prob.goal' s))).get
        (planner_isSome_implies_astar_isSome prob heur ret_plan)).2.cost := by
  obtain ⟨ret, hret⟩ :=
    Option.isSome_iff_exists.mp (planner_isSome_implies_astar_isSome prob heur ret_plan)
  obtain ⟨pl, hpl1⟩ : ∃ pl, planner prob heur = some pl :=
    Option.isSome_iff_exists.mp ret_plan
  rw [Option.get_of_eq_some _ hpl1, Option.get_of_eq_some _ hret,
      WeightedDiGraph.Path.cost_same]
  simp only [planner, trans_of_STRIPS_goals, hret, Option.some.injEq] at hpl1
  subst hpl1
  exact walk_to_strips_path_cost_eq prob ret.2.val _

/-- For any plan, its STRIPS path cost ≥ the A* optimal graph path cost. -/
lemma plan_cost_ge_astar {n : ℕ} (prob : PlanningTask n) (heur : State' n → ℕ∞)
    (admissible : heur_admissible prob heur)
    (astar_some : Option.isSome (NatGraph.astar_multigoal (g := trans_of_STRIPS prob)
      heur prob.init'
      ((List.finRange (2^n)).filter (fun s => satisfies' prob.goal' s))))
    (plan : Plan prob prob.init) :
    plan.path.cost ≥
      ((NatGraph.astar_multigoal (g := trans_of_STRIPS prob) heur prob.init'
        ((List.finRange (2^n)).filter (fun s => satisfies' prob.goal' s))).get astar_some).2.cost := by
  obtain ⟨g', hg'⟩ : ∃ g' : State' n, convertState g' = plan.last := by
    convert state_has_bitvec plan.last;
    exact Classical.decPred (Set.Mem plan.last)
  -- By `strips_path_has_cheaper_walk`, get walk w with w.cost ≤ plan.path.cost.
  obtain ⟨w, hw⟩ : ∃ w : WeightedDiGraph.Walk (G := trans_of_STRIPS prob) prob.init' g', w.cost ≤ (hg' ▸ plan.path).cost := by
    apply strips_path_has_cheaper_walk;
  obtain ⟨p, hp⟩ : ∃ p : (trans_of_STRIPS prob).Path prob.init' g', p.cost ≤ w.cost := by
    exact WeightedDiGraph.Walk.cheaper_path_exists w
  have h_optimal : (NatGraph.astar_multigoal (g := trans_of_STRIPS prob) heur prob.init'
    ((List.finRange (2^n)).filter (fun s => satisfies' prob.goal' s))).get astar_some |>.2.cost ≤ p.cost := by
      apply astar_multigoal_cross_goal_optimal;
      · have h_admissible' := admissible'_of_admissible prob heur admissible
        intro v goal goal_in_goals gp
        have goal_in_goals' : goal ∈ trans_of_STRIPS_goals prob := by
          rw [mem_trans_of_STRIPS_goals_iff]
          exact (List.mem_filter.mp goal_in_goals).2
        exact h_admissible' v goal goal_in_goals' gp
      · simp
        constructor
        · exact ⟨ g'.toFin, rfl ⟩
        · have gs := plan.goal
          rw [← hg'] at gs
          exact (satisfies'_iff prob.goal' g').mp (GoalState_implies_satisfies' prob g' gs)
  grind



lemma planner_optimal {n : ℕ} (prob : PlanningTask n) (heur : State' n → ℕ∞)
  (admissible : heur_admissible prob heur)
  (ret_plan : (planner prob heur).isSome):
  ∀ plan : Plan prob prob.init, plan.path.cost ≥ ((planner prob heur).get ret_plan).path.cost := by
  intro plan
  rw [planner_path_cost_eq_astar]
  exact plan_cost_ge_astar prob heur admissible (planner_isSome_implies_astar_isSome prob heur ret_plan) plan
