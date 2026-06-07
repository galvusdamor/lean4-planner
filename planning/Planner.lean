import SearchAlgorithms.AStar
import planning.Heuristics

namespace Validator


def planner {n : ℕ} (prob : STRIPS n) (heur : State' n → ℕ): Option (Plan prob prob.init) :=
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
      exact goal'_in_goals.2

    let path : Path prob (convertState ini) (convertState goal') := walk_to_strips_path prob ret.2.val sat
    have goal_sat : prob.GoalState (convertState goal') := by
      unfold STRIPS.GoalState
      unfold convertVarSet convertState
      intro x x_in_goal'
      unfold satisfies' at sat
      simp only [Fin.getElem_fin, List.all_eq_true] at sat
      apply sat
      simp_all
    let plan : Plan prob prob.init := Plan.mk (convertState ret.fst) path goal_sat
    Option.some plan



lemma planner_complete {n : ℕ} (prob : STRIPS n) (heur : State' n → ℕ):
      planner prob heur = Option.none → Unsolvable prob := by
  intro ret_none
  unfold Unsolvable UnsolvableState
  constructor
  intro plan
  let plan_path : Path prob prob.init plan.last := plan.path
  unfold STRIPS.init at plan_path
  have last_dec : DecidablePred (Set.Mem plan.last) := last_dec prob prob.init' plan.last plan_path
  obtain ⟨goal',goal_eq_goal'⟩ := state_has_bitvec plan.last
  rw [←goal_eq_goal'] at plan_path
  let walk := strips_path_to_walk prob plan_path


  unfold planner at ret_none
  simp at ret_none
  split at ret_none
  · expose_names
    let goals : List (State' n) := trans_of_STRIPS_goals prob

    have no_goal_path := mt (NatGraph.astar_multigoal_is_complete heur prob.init' goals) (by simp ; apply heq)
    push_neg at no_goal_path
    have goal'_in_goals : goal' ∈ goals := by
      unfold goals
      simp [trans_of_STRIPS_goals]
      constructor
      · grind only
      · have gs := plan.goal
        unfold STRIPS.GoalState at gs
        unfold satisfies'
        simp
        intro x x_in_goal'
        rw [←goal_eq_goal'] at gs
        unfold convertVarSet convertState at gs
        simp_all only [ne_eq, not_true_eq_false, Subtype.forall, imp_false, List.coe_toFinset, Fin.getElem_fin, Set.setOf_subset_setOf]
    obtain ⟨path,_⟩ := walk.shorter_path_exists
    specialize no_goal_path goal' goal'_in_goals path
    contradiction
  · grind -- some = none




/-- The A* multigoal result is optimal across all goals: its graph path cost is ≤ any graph path
    to any goal in the goals list. -/
lemma astar_multigoal_cross_goal_optimal {n : ℕ} (prob : STRIPS n) (heur : State' n → ℕ)
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
      (g := (trans_of_STRIPS prob).add_artificial_goal goals)
      (NatGraph.opt_heur heur) (some prob.init') none = some aug_path := by
    exact Option.isSome_iff_exists.mp
      (NatGraph.astar_multigoal_some_implies_astar_some heur prob.init' goals returned_path)
  obtain ⟨aug_path, h_eq⟩ := h_some
  -- The augmented path is optimal
  have aug_optimal : aug_path.is_cheapest := by
    have aug_ret : Option.isSome (NatGraph.astar
        (g := (trans_of_STRIPS prob).add_artificial_goal goals)
        (NatGraph.opt_heur heur) (some prob.init') none) := by
      rw [h_eq]; simp
    have h := NatGraph.astar_is_optimal
      (g := (trans_of_STRIPS prob).add_artificial_goal goals)
      (NatGraph.opt_heur heur) (some prob.init') none
      (NatGraph.opt_heur_admissible heur admissible) aug_ret
    have h_get : (NatGraph.astar
        (g := (trans_of_STRIPS prob).add_artificial_goal goals)
        (NatGraph.opt_heur heur) (some prob.init') none).get aug_ret = aug_path := by
      simp [h_eq]
    rw [h_get] at h
    exact h
  -- Lift p to augmented path
  obtain ⟨aug_p, h_cost_eq⟩ := NatGraph.lift_path_to_augmented_cost
    (G := trans_of_STRIPS prob) goal_in_goals p
  -- Chain: returned.cost ≤ aug_path.cost ≤ aug_p.cost = p.cost
  have h1 : aug_path.cost ≤ p.cost := calc
    aug_path.cost ≤ aug_p.cost := aug_optimal aug_p
    _ = p.cost := h_cost_eq
  have h2 := NatGraph.astar_multigoal_cost_le_aug
    heur prob.init' goals returned_path aug_path h_eq
  exact le_trans h2 h1

/-
PROBLEM
When planner returns some, the underlying A* also returns some.

PROVIDED SOLUTION
Unfold planner. Since ret_plan says planner returns some, the A* match is in the some case. The planner's path is walk_to_strips_path of the A* result walk. By walk_to_strips_path_cost_eq, its cost = the graph walk cost.

For any plan:
1. Get DecidablePred for plan.last via last_dec
2. Get BitVec g' for plan.last via state_has_bitvec
3. Rewrite plan.path to go from convertState init' to convertState g'
4. By strips_path_has_cheaper_walk, get graph walk with cost ≤ plan.path.cost
5. By Walk.cheaper_path_exists, get graph Path with cost ≤ walk cost
6. g' is in the goals list (satisfies goal condition)
7. By astar_multigoal_cross_goal_optimal, A* result cost ≤ graph Path cost
8. Chain inequalities: planner.path.cost = graph walk cost ≤ any plan.path.cost

Unfold planner at ret_plan. The planner matches on astar_multigoal result. If astar_multigoal returns none, planner returns none, so ret_plan (isSome of none) would be false. Contradiction. So astar_multigoal returns some.
-/
lemma planner_isSome_implies_astar_isSome {n : ℕ} (prob : STRIPS n) (heur : State' n → ℕ)
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

/-
PROBLEM
The planner's path cost equals the A* multigoal result's graph path cost.

PROVIDED SOLUTION
Unfold planner at ret_plan and the goal. Split on the astar_multigoal match. In the none case, contradiction with ret_plan. In the some case with result `ret`, the planner's plan has path = walk_to_strips_path prob ret.2.val sat. By walk_to_strips_path_cost_eq, this cost = ret.2.val.cost. And ret.2.val.cost = ret.2.cost by WeightedDiGraph.Path.cost_same. And (astar_multigoal.get ...).2 = ret.2 in the some case. So the costs match.

Unfold planner at both ret_plan and the goal. Split on the match of astar_multigoal. In the none case, contradiction with ret_plan (Option.isSome none = false). In the some case with ret, the planner's plan has path = walk_to_strips_path prob ret.2.val sat, so (planner prob).get.path.cost = (walk_to_strips_path prob ret.2.val sat).cost = ret.2.val.cost (by walk_to_strips_path_cost_eq). And the RHS is ((astar_multigoal ...).get ...).2.cost = ret.2.cost = ret.2.val.cost (by WeightedDiGraph.Path.cost_same). So both sides equal ret.2.val.cost.
-/
lemma planner_path_cost_eq_astar {n : ℕ} (prob : STRIPS n) (heur : State' n → ℕ)
    (ret_plan : (planner prob heur).isSome) :
    ((planner prob heur).get ret_plan).path.cost =
      ((NatGraph.astar_multigoal (g := trans_of_STRIPS prob) heur prob.init'
        ((List.finRange (2^n)).filter (fun s => satisfies' prob.goal' s))).get
        (planner_isSome_implies_astar_isSome prob heur ret_plan)).2.cost := by
  unfold planner at ret_plan
  generalize_proofs at *;
  unfold planner;
  nontriviality;
  rename_i h₁ h₂ h₃;
  obtain ⟨ ret, hret ⟩ := Option.isSome_iff_exists.mp h₂;
  simp
  convert walk_to_strips_path_cost_eq prob ret.2.val _ using 1;
  any_goals solve_by_elim;
  · unfold Option.get; unfold trans_of_STRIPS_goals
    simp_all only [BitVec.natCast_eq_ofNat, List.pure_def, List.bind_eq_flatMap, Option.isSome_some]
    obtain ⟨fst, snd⟩ := ret
    obtain ⟨val, property⟩ := fst
    obtain ⟨val_1, property_1⟩ := snd
    simp_all only [BitVec.natCast_eq_ofNat, List.pure_def, List.bind_eq_flatMap]
    split
    rename_i _ _ _ _ heq _
    simp_all only [Option.some.injEq, heq_eq_eq]
    subst heq
    simp_all only [Option.isSome_some]
  · congr! 2;
    · congr! 1
      exact Option.get_of_eq_some h₂ hret
    · congr! 2;
    · congr! 3;
    · congr! 1;
      exact Option.get_of_eq_some h₂ hret

/-
PROBLEM
For any plan, its STRIPS path cost ≥ the A* optimal graph path cost.

PROVIDED SOLUTION
Given plan : Plan prob prob.init:
1. plan.path is a Path from prob.init to plan.last. prob.init = convertState prob.init'.
2. Get DecidablePred for plan.last using last_dec prob prob.init' plan.last plan.path.
3. Get g' : State' n with convertState g' = plan.last via state_has_bitvec plan.last.
4. Rewrite plan.path: it's now Path prob (convertState prob.init') (convertState g').
5. By strips_path_has_cheaper_walk, get walk w with w.cost ≤ plan.path.cost.
6. By Walk.cheaper_path_exists (or shorter_path_exists), get graph Path p with p.cost ≤ w.cost.
7. Show g' is in the goals list: g' ∈ (List.finRange (2^n)).filter (satisfies' prob.goal').
   This holds because plan.last is a goal state (plan.goal says GoalState plan.last), and
   convertState g' = plan.last, so satisfies' prob.goal' g' = true.
8. By astar_multigoal_cross_goal_optimal, the A* result cost ≤ p.cost.
9. Chain: A* cost ≤ p.cost ≤ w.cost ≤ plan.path.cost.

1. Have plan.path : Path prob prob.init plan.last where prob.init = convertState prob.init' (unfold STRIPS.init).
2. Get DecidablePred for plan.last: haveI := last_dec prob prob.init' plan.last (show Path prob (convertState prob.init') plan.last from plan.path).
3. Get g' with hg' : convertState g' = plan.last via state_has_bitvec.
4. The plan.path, rewritten via hg', is a Path from (convertState prob.init') to (convertState g'): use hg' ▸ plan.path.
5. By strips_path_has_cheaper_walk prob (hg' ▸ plan.path), get walk w with w.cost ≤ plan.path.cost.
   (The rewriting preserves cost since path cost depends on structure, not endpoints.)
6. By Walk.cheaper_path_exists w, get graph Path p with p.cost ≤ w.cost.
7. g' ∈ goals: unfold the filter, show satisfies' prob.goal' g' from plan.goal (GoalState plan.last) and hg'. For the Finset membership, use List.mem_filter and the range condition.
8. By astar_multigoal_cross_goal_optimal, get A* cost ≤ p.cost.
9. Chain: A* cost ≤ p.cost ≤ w.cost ≤ plan.path.cost. So plan.path.cost ≥ A* cost.
-/
lemma plan_cost_ge_astar {n : ℕ} (prob : STRIPS n) (heur : State' n → ℕ)
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
      simp
      · have h_admissible' := admissible'_of_admissible prob heur admissible
        unfold NatGraph.admissible'
        intro v goal is_goal
        unfold NatGraph.cost_ge
        intro gp
        have goal_in_goals : goal ∈ trans_of_STRIPS_goals prob := by
          rw [mem_trans_of_STRIPS_goals_iff]
          simp at is_goal
          exact is_goal.2
        exact h_admissible' v goal goal_in_goals gp
      · simp
        constructor
        · exact ⟨ g'.toFin, rfl ⟩
        · have := plan.goal
          unfold STRIPS.GoalState at this; unfold convertState at hg'
          unfold convertVarSet at this
          unfold satisfies'
          simp_all [ Set.subset_def ]
          exact fun x hx => hg'.symm.subset ( this x hx )
  grind



lemma planner_optimal {n : ℕ} (prob : STRIPS n) (heur : State' n → ℕ)
  (admissible : heur_admissible prob heur)
  (ret_plan : (planner prob heur).isSome):
  ∀ plan : Plan prob prob.init, plan.path.cost ≥ ((planner prob heur).get ret_plan).path.cost := by
  intro plan
  rw [planner_path_cost_eq_astar]
  exact plan_cost_ge_astar prob heur admissible (planner_isSome_implies_astar_isSome prob heur ret_plan) plan
