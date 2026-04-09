import Validator.PlanningTask.Core
import Validator.PlanningTask.Basic
import Graphlib.NatGraph
import Graphlib.Planning
import Graphlib.Heuristics
import Graphlib.Planner

import Graphlib.temp

import Mathlib.Logic.Lemmas
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Vector.Basic

namespace Validator

/-! ### Casting plans between STRIPS problems with the same actions and goals -/

/-- Replace the initial state of a STRIPS problem. -/
def replace_init_state {n : ℕ} (prob : STRIPS n) (s : State' n) : STRIPS n :=
  STRIPS.mk prob.varNames prob.actions' s prob.goal'

/-- Cast a path from `prob` to `replace_init_state prob s`. -/
noncomputable def cast_path_to_replace {n : ℕ} (prob : STRIPS n) (s : State' n) {s1 s2 : State n}
    (path : Path prob s1 s2) : Path (replace_init_state prob s) s1 s2 := by
  induction path with
  | empty s => exact Path.empty s
  | cons a s2 ha succ rest ih => exact Path.cons a s2 ha succ ih

/-- Cast a path from `replace_init_state prob s` to `prob`. -/
noncomputable def cast_path_from_replace {n : ℕ} (prob : STRIPS n) (s : State' n) {s1 s2 : State n}
    (path : Path (replace_init_state prob s) s1 s2) : Path prob s1 s2 := by
  induction path with
  | empty s => exact Path.empty s
  | cons a s2 ha succ rest ih => exact Path.cons a s2 ha succ ih

lemma cast_path_to_replace_cost {n : ℕ} (prob : STRIPS n) (s : State' n) {s1 s2 : State n}
    (path : Path prob s1 s2) : (cast_path_to_replace prob s path).cost = path.cost := by
  induction path with
  | empty => rfl
  | cons a s2 ha succ rest ih =>
    unfold cast_path_to_replace; simp only [Path.cost]; exact congrArg (· + a.cost) ih

lemma cast_path_from_replace_cost {n : ℕ} (prob : STRIPS n) (s : State' n) {s1 s2 : State n}
    (path : Path (replace_init_state prob s) s1 s2) : (cast_path_from_replace prob s path).cost = path.cost := by
  induction path with
  | empty => rfl
  | cons a s2 ha succ rest ih =>
    unfold cast_path_from_replace; simp only [Path.cost]; exact congrArg (· + a.cost) ih

/-- Cast a plan from `prob` to `replace_init_state prob s`. -/
noncomputable def cast_plan_to_replace {n : ℕ} (prob : STRIPS n) (s : State' n)
    (plan : Plan prob (convertState s)) : Plan (replace_init_state prob s) (convertState s) :=
  ⟨plan.last, cast_path_to_replace prob s plan.path, plan.goal⟩

/-- Cast a plan from `replace_init_state prob s` to `prob`. -/
noncomputable def cast_plan_from_replace {n : ℕ} (prob : STRIPS n) (s : State' n)
    (plan : Plan (replace_init_state prob s) (convertState s)) : Plan prob (convertState s) :=
  ⟨plan.last, cast_path_from_replace prob s plan.path, plan.goal⟩

lemma replace_init_state_init {n : ℕ} (prob : STRIPS n) (s : State' n) :
    (replace_init_state prob s).init = convertState s := rfl

/-! ### Perfect heuristic -/

def perfect_heuristic {n : ℕ} (prob : STRIPS n) (s : State' n) : ℕ :=
  let replace_init := STRIPS.mk prob.varNames prob.actions' s prob.goal'
  let opt_ret := planner replace_init (fun _ => 0)
  match opt_ret with
  | .none => (2^n) * (max_action_cost prob)
  | .some ret =>
      ret.2.cost

/-- When a state is unsolvable, the planner on the corresponding replaced problem returns none. -/
private lemma planner_none_of_unsolvable {n : ℕ} (prob : STRIPS n) (v : State' n)
    (hv : IsEmpty (Plan prob (convertState v))) :
    planner (replace_init_state prob v) (fun _ => 0) = none := by
  by_contra h_ne
  cases h : planner (replace_init_state prob v) (fun _ => 0) with
  | none => exact h_ne h
  | some ret => exact hv.false (cast_plan_from_replace prob v ret)

lemma perferct_heuristic_is_perfect {n : ℕ} (prob : STRIPS n):
  heur_is_perfect prob (perfect_heuristic prob) := by
    refine ⟨?_, ?_, ?_⟩
    · -- Admissibility
      intro plan plan_1
      unfold perfect_heuristic
      cases h : planner ( STRIPS.mk prob.varNames prob.actions' plan prob.goal' ) ( fun _ => 0 ) <;> simp_all +decide
      · have := planner_complete ( STRIPS.mk prob.varNames prob.actions' plan prob.goal' ) ( fun _ => 0 ) h
        contrapose! this
        exact ⟨ ⟨ plan_1.last, cast_path_to_replace prob plan plan_1.path, plan_1.goal ⟩ ⟩
      · have := planner_optimal ( STRIPS.mk prob.varNames prob.actions' plan prob.goal' ) ( fun _ => 0 ) ( zero_heur_admissible _ )
        convert this ( by simp +decide [ h ] ) ( cast_plan_to_replace prob plan plan_1 ) |> le_trans <| ?_
        · grind
        · grind
        · exact le_of_eq ( cast_path_to_replace_cost prob plan plan_1.path )
    · -- Solvable states have optimal plan
      intro v hv
      unfold perfect_heuristic
      obtain ⟨plan, hplan⟩ := hv
      cases h : planner ( STRIPS.mk prob.varNames prob.actions' v prob.goal' ) ( fun _ => 0 ) <;> simp_all +decide
      · have := planner_complete ( STRIPS.mk prob.varNames prob.actions' v prob.goal' ) ( fun _ => 0 ) h
        contrapose! this
        exact ⟨ ⟨ plan, cast_path_to_replace prob v hplan, by assumption ⟩ ⟩
      · rename_i hplan'
        exact ⟨ ⟨ hplan'.last, cast_path_from_replace prob v hplan'.path, hplan'.goal ⟩,
               cast_path_from_replace_cost prob v hplan'.path ⟩
    · -- Unsolvable states have high value
      intro v hv
      unfold perfect_heuristic
      have h_none := planner_none_of_unsolvable prob v hv
      simp [replace_init_state] at h_none
      simp [h_none]


/-
weak because the prefect heuristic has a particular value for solvable states and admissible heuristics can return arbirarily high values for that heuristic
-/
lemma perfect_heuristic_weak_dominates_admissible {n : ℕ} (prob : STRIPS n) (h : State' n → ℕ):
    heur_admissible prob h → ∀ s : State' n, Nonempty (Plan prob (convertState s)) → (perfect_heuristic prob) s ≥ h s := by
      intro h_admissible s hs_solvable
      obtain ⟨plan, hplan⟩ : ∃ plan : Plan prob (convertState s), plan.path.cost = perfect_heuristic prob s := by
        convert perferct_heuristic_is_perfect prob
        constructor <;> intro h <;> cases h
        · exact perferct_heuristic_is_perfect prob
        · grind
      exact hplan ▸ h_admissible s plan


-- A perfect heuristic has for all solvable states that the heuristic value is determine by considering the "cheapest" applicable action and the heuristic of the successor
def perfect_heuristic_invariant {n : ℕ} (prob : STRIPS n) (h : State' n → ℕ):=
  (∀ s : State' n, Nonempty (Plan prob (convertState s)) →
  if satisfies' prob.goal' s  then h s = 0
  else
  (
    let appli : List (Action n) := prob.actions'.filter (fun a => applicable' a s)

    appli ≠ [] ∧ Option.some (h s) = (appli.map (fun a => a.cost + h (successor' a s))).min?
  ))
  ∧
  ∀ s : State' n, IsEmpty (Plan prob (convertState s)) →
    h s ≥ (2^n) * (max_action_cost prob)

/-! ### Helper: the invariant implies h(s) ≤ a.cost + h(succ(a,s)) -/

lemma invariant_gives_le {n : ℕ} (prob : STRIPS n) (h : State' n → ℕ)
    (hi : perfect_heuristic_invariant prob h)
    (s : State' n) (hs : Nonempty (Plan prob (convertState s)))
    (a : Action n) (ha : a ∈ prob.actions') (happ : applicable' a s = true) :
    h s ≤ a.cost + h (successor' a s) := by
      obtain ⟨ hi, _ ⟩ := hi
      specialize hi s hs
      split_ifs at hi
      case pos hi =>
        grind
      case neg hi =>
        obtain ⟨ _, heq ⟩ := hi
        have h_min_le : ∀ {l : List ℕ}, a.cost + h (successor' a s) ∈ l → (List.min? l).getD 0 ≤ a.cost + h (successor' a s) := by
          exact fun {l} a_1 => List.min?_getD_le_of_mem a_1;
        grind

/-! ### Path cost bound via invariant -/

/-- Auxiliary: for any path from a solvable state, cost ≥ h(start), using the invariant
    and goal-awareness. This mirrors `strips_path_cost_ge_heur` from Heuristics.lean. -/
private lemma path_cost_ge_heur_of_invariant {n : ℕ} (prob : STRIPS n) (h : State' n → ℕ)
    (ga : heur_goal_aware prob h)
    (hi : perfect_heuristic_invariant prob h)
    (k : ℕ) {start : State' n} {goal : State n}
    (path : Path prob (convertState start) goal)
    (hlen : path.length ≤ k)
    (goal_state : prob.GoalState goal) :
    path.cost ≥ h start := by
  induction k generalizing start goal with
  | zero =>
    generalize hs : convertState start = s at path
    cases path with
    | empty =>
      simp [Path.cost]
      exact ga start (GoalState_implies_satisfies' prob start (hs ▸ goal_state))
    | cons => simp [Path.length] at hlen
  | succ k ih =>
    generalize hs : convertState start = s at path
    cases path with
    | empty =>
      simp [Path.cost]
      exact ga start (GoalState_implies_satisfies' prob start (hs ▸ goal_state))
    | cons a s2 ha succ path' =>
      subst hs
      haveI := successor_dec a (convertState start) s2 succ
      obtain ⟨s2', rfl⟩ := state_has_bitvec s2
      have a_app : applicable' a start = true := successor_implies_applicable succ
      have s2'_eq : s2' = successor' a start :=
        is_successor'_eq_successor' a start s2' (successor_implies_is_successor succ)
      subst s2'_eq
      have ih' := ih path' (by simp [Path.length] at hlen; exact hlen) goal_state
      have h_solvable : Nonempty (Plan prob (convertState start)) :=
        ⟨⟨goal, Path.cons a _ ha succ path', goal_state⟩⟩
      calc h start
          ≤ a.cost + h (successor' a start) :=
            invariant_gives_le prob h hi start h_solvable a (mem_actions'_of_mem_actions ha) a_app
        _ ≤ a.cost + path'.cost := Nat.add_le_add_left ih' _
        _ = path'.cost + a.cost := Nat.add_comm _ _
        _ = (Path.cons a (convertState (successor' a start)) ha succ path').cost := by simp [Path.cost]

lemma goal_aware_of_perfect_heuristic_invariant {n : ℕ} (prob : STRIPS n) (h : State' n → ℕ):
  perfect_heuristic_invariant prob h → heur_goal_aware prob h := by
    intro ⟨invar, _⟩ s s_is_goal
    have goal_state := satisfies'_implies_GoalState prob s s_is_goal
    have hs : Nonempty (Plan prob (convertState s)) :=
      ⟨⟨convertState s, Path.empty _, goal_state⟩⟩
    specialize invar s hs
    simp [s_is_goal] at invar
    exact invar

lemma admissible_of_perfect_heuristic_invariant {n : ℕ} (prob : STRIPS n) (h : State' n → ℕ):
  perfect_heuristic_invariant prob h → heur_admissible prob h := by
  intro hi v plan
  exact path_cost_ge_heur_of_invariant prob h (goal_aware_of_perfect_heuristic_invariant prob h hi) hi plan.path.length plan.path (le_refl _) plan.goal

/-! ### Helper lemmas for perfect_heuristic_has_invariant -/

/-- A perfect heuristic is goal-aware: h(s) = 0 when s satisfies the goal. -/
lemma perfect_is_goal_aware {n : ℕ} (prob : STRIPS n) (h : State' n → ℕ)
    (hp : heur_is_perfect prob h) (s : State' n)
    (hsat : satisfies' prob.goal' s = true) : h s = 0 := by
  have hadm := hp.1
  have goal_state := satisfies'_implies_GoalState prob s hsat
  let plan : Plan prob (convertState s) := ⟨convertState s, Path.empty _, goal_state⟩
  have hle := hadm s plan
  show h s = 0
  simp only [plan, Path.cost, Nat.le_zero] at hle
  exact hle

/-
If `applicable' a s`, then `Successor a (convertState s) (convertState (successor' a s))`.
-/
lemma Successor_of_applicable' {n : ℕ} (a : Action n) (s : State' n)
    (happ : applicable' a s = true) :
    Successor a (convertState s) (convertState (successor' a s)) := by
      constructor;
      · intro x hx;
        unfold convertState; simp_all +decide [ Action.pre ] ;
        unfold convertVarSet at hx; simp_all +decide [ applicable' ] ;
        unfold satisfies' at happ; aesop;
      · -- By definition of successor', we know that for every variable x, x is in the successor state exactly when it's in the original state and not in del, or in add.
        have h_succ_vars : ∀ x : Fin n, x ∈ convertState (successor' a s) ↔ x ∈ convertState s \ a.del ∪ a.add := by
          intro x
          simp [convertState, successor', Action.add, Action.del];
          rw [ BitVec.getElem_ofBoolListLE ];
          unfold convertVarSet; aesop;
        exact Set.ext h_succ_vars

/-
A solvable non-goal state has at least one applicable action in the actions list.
-/
lemma solvable_non_goal_has_applicable {n : ℕ} (prob : STRIPS n) (s : State' n)
    (hs : Nonempty (Plan prob (convertState s)))
    (hng : satisfies' prob.goal' s = false) :
    (prob.actions'.filter (fun a => applicable' a s)) ≠ [] := by
      obtain ⟨ plan, hplan ⟩ := hs;
      obtain ⟨a, ha⟩ : ∃ a : Action n, a ∈ prob.actions ∧ applicable' a s = true := by
        cases hplan <;> simp_all +decide [ applicable' ];
        · exact False.elim <| hng.not_gt <| GoalState_implies_satisfies' prob s ‹_›;
        · use ‹Action n›; simp_all +decide [ Successor ] ;
          rename_i a s2 ha π succ;
          unfold satisfies';
          simp_all +decide [ Applicable ];
          intro x hx; have := succ.1 ( show x ∈ a.pre from by
                                        exact Finset.mem_coe.mpr ( List.mem_toFinset.mpr hx ) ) ; aesop;
      exact List.ne_nil_of_mem ( List.mem_filter.mpr ⟨ mem_actions'_of_mem_actions ha.1, ha.2 ⟩ )

/-
For a perfect heuristic, h(s) ≤ a.cost + h(succ(a,s)) for all applicable a with
    solvable successor. Constructs a plan from s by prepending a to the optimal plan from
    succ(a,s), then uses admissibility.
-/
lemma perfect_le_action_succ {n : ℕ} (prob : STRIPS n) (h : State' n → ℕ)
    (hp : heur_is_perfect prob h) (s : State' n)
    (a : Action n) (ha : a ∈ prob.actions')
    (happ : applicable' a s = true)
    (hsolv_succ : Nonempty (Plan prob (convertState (successor' a s)))) :
    h s ≤ a.cost + h (successor' a s) := by
      have hadm := hp.1
      obtain ⟨plan_succ, hplan_succ⟩ : ∃ plan_succ : Plan prob (convertState (successor' a s)),
          plan_succ.2.cost = h (successor' a s) := hp.2.1 (successor' a s) hsolv_succ
      have h_plan_succ : ∃ plan_succ' : Plan prob (convertState s), plan_succ'.2.cost ≤ a.cost + h (successor' a s) := by
        use ⟨plan_succ.last, Path.cons a (convertState (successor' a s)) (by
        exact List.mem_dedup.mpr ha) (Successor_of_applicable' a s happ) plan_succ.path, plan_succ.goal⟩
        generalize_proofs at *
        exact add_comm a.cost _ ▸ add_le_add_left hplan_succ.le _
      obtain ⟨ plan_succ', hplan_succ' ⟩ := h_plan_succ
      exact le_trans (hadm s plan_succ') hplan_succ'

/-
Any plan from a solvable state has a graph path whose cost is at most
    2^n * max_action_cost and whose underlying walk converts back to a STRIPS plan
    of the same cost.
-/
private lemma exists_plan_cost_le_bound {n : ℕ} (prob : STRIPS n) (s : State' n)
    (hs : Nonempty (Plan prob (convertState s))) :
    ∃ plan : Plan prob (convertState s), plan.path.cost ≤ 2 ^ n * max_action_cost prob := by
  obtain ⟨ plan, hplan ⟩ := hs;
  -- Use `last_dec prob s plan.last plan.path` to get DecidablePred for plan.last.
  have hdec : ∃ g' : State' n, convertState g' = plan := by
    have := Validator.last_dec prob s plan;
    convert state_has_bitvec plan;
    exact this hplan;
  obtain ⟨ g', rfl ⟩ := hdec;
  obtain ⟨ w, hw ⟩ := strips_path_has_cheaper_walk prob hplan;
  obtain ⟨ p, hp ⟩ := WeightedDiGraph.Walk.cheaper_path_exists w;
  refine' ⟨ ⟨ convertState g', walk_to_strips_path prob p.val ( GoalState_implies_satisfies' prob g' ‹_› ), satisfies'_implies_GoalState prob g' ( GoalState_implies_satisfies' prob g' ‹_› ) ⟩, _ ⟩;
  have := graph_path_cost_le_bound prob s g' p;
  convert this using 1;
  convert walk_to_strips_path_cost_eq prob p.val ( GoalState_implies_satisfies' prob g' ‹_› ) using 1

/-- For a perfect heuristic at a solvable state, h(s) ≤ 2^n * max_action_cost.
    This follows because there exists a plan with cost ≤ 2^n * max_action_cost,
    and by admissibility h(s) ≤ that plan's cost. -/
lemma perfect_heur_solvable_le_bound {n : ℕ} (prob : STRIPS n) (h : State' n → ℕ)
    (hp : heur_is_perfect prob h) (s : State' n)
    (hs : Nonempty (Plan prob (convertState s))) :
    h s ≤ 2 ^ n * max_action_cost prob := by
  obtain ⟨plan, hplan⟩ := exists_plan_cost_le_bound prob s hs
  exact le_trans (hp.1 s plan) hplan

/-
For a perfect heuristic at a solvable non-goal state, there exists an applicable action
    achieving h(s) = a.cost + h(succ(a,s)). Uses the optimal plan: its first action a₀ gives
    h(s) = a₀.cost + tail.cost ≥ a₀.cost + h(succ(a₀,s)) (admissibility of tail) and
    h(s) ≤ a₀.cost + h(succ(a₀,s)) (from `perfect_le_action_succ`).
-/
lemma perfect_achieves_min {n : ℕ} (prob : STRIPS n) (h : State' n → ℕ)
    (hp : heur_is_perfect prob h) (s : State' n)
    (hs : Nonempty (Plan prob (convertState s)))
    (hng : satisfies' prob.goal' s = false) :
    ∃ a ∈ prob.actions'.filter (fun a => applicable' a s),
      a.cost + h (successor' a s) = h s := by
        -- By hp.2.1 s hs, get plan with plan.path.cost = h s.
        obtain ⟨plan, hplan⟩ := hp.2.1 s hs
        rcases plan with ⟨last, path, goal_sat⟩
        rcases path with ( _ | ⟨a₀, s2, ha₀, succ₀, rest⟩ ) <;> simp_all +decide;
        · exact absurd ( GoalState_implies_satisfies' prob s goal_sat ) ( by aesop );
        · -- By the definition of successor, we know that s2 is the successor state of a₀ and s.
          have hs2 : s2 = convertState (successor' a₀ s) := by
            obtain ⟨ _, foo ⟩ := succ₀
            generalize_proofs at *;
            ext i; simp [foo, successor'];
            unfold convertState; simp +decide [ BitVec.getElem_ofBoolListLE ] ;
            simp +decide [ or_comm, Action.add, Action.del ];
            unfold convertVarSet; simp +decide [ and_comm ] ;
          subst hs2;
          have := hp.1 ( successor' a₀ s ) ⟨ last, rest, goal_sat ⟩ ; simp_all +decide [ Path.cost ] ;
          exact ⟨ a₀, ⟨ mem_actions'_of_mem_actions ha₀, successor_implies_applicable succ₀ ⟩,
            by have := perfect_le_action_succ prob h hp s a₀ ( mem_actions'_of_mem_actions ha₀ )
                           ( successor_implies_applicable succ₀ ) ⟨ last, rest, goal_sat ⟩; omega ⟩

/-- For a perfect heuristic, h(s) ≤ a.cost + h(succ(a,s)) for all applicable actions,
    including when the successor is unsolvable. When the successor is unsolvable,
    h(succ(a,s)) ≥ 2^n * max_action_cost ≥ h(s). -/
lemma perfect_le_action_succ_general {n : ℕ} (prob : STRIPS n) (h : State' n → ℕ)
    (hp : heur_is_perfect prob h) (s : State' n)
    (hs : Nonempty (Plan prob (convertState s)))
    (a : Action n) (ha : a ∈ prob.actions')
    (happ : applicable' a s = true) :
    h s ≤ a.cost + h (successor' a s) := by
  by_cases hsolv : Nonempty (Plan prob (convertState (successor' a s)))
  · exact perfect_le_action_succ prob h hp s a ha happ hsolv
  · -- successor is unsolvable
    rw [not_nonempty_iff] at hsolv
    have h_bound := hp.2.2 (successor' a s) hsolv
    have h_le := perfect_heur_solvable_le_bound prob h hp s hs
    calc h s ≤ 2 ^ n * max_action_cost prob := h_le
      _ ≤ h (successor' a s) := h_bound
      _ ≤ a.cost + h (successor' a s) := Nat.le_add_left _ _

lemma perfect_heuristic_has_invariant {n : ℕ} (prob : STRIPS n) (h : State' n → ℕ):
    heur_is_perfect prob h → perfect_heuristic_invariant prob h := by
  intro hp
  constructor
  · -- Solvable states part
    intro s hs
    split_ifs with hgoal
    · exact perfect_is_goal_aware prob h hp s hgoal
    · have hng : satisfies' prob.goal' s = false := by simpa using hgoal
      constructor
      · exact solvable_non_goal_has_applicable prob s hs hng
      · rw [eq_comm, List.min?_eq_some_iff]
        constructor
        · -- h s is achieved by some applicable action
          obtain ⟨a, ha_mem, ha_eq⟩ := perfect_achieves_min prob h hp s hs hng
          rw [← ha_eq]
          exact List.mem_map.mpr ⟨a, ha_mem, rfl⟩
        · -- h s ≤ every element
          intro x hx
          rw [List.mem_map] at hx
          obtain ⟨a, ha_mem, rfl⟩ := hx
          rw [List.mem_filter] at ha_mem
          exact perfect_le_action_succ_general prob h hp s hs a ha_mem.1 ha_mem.2
  · -- Unsolvable states part
    exact hp.2.2

-- weakening of perfect invariant: the heuristic can also be lower. That can't make it inadmissible
def weaker_than_perfect_heuristic_invariant {n : ℕ} (prob : STRIPS n) (h : State' n → ℕ):=
  ∀ s : State' n, Nonempty (Plan prob (convertState s)) →
  if satisfies' prob.goal' s  then h s = 0
  else
  (
    let appli : List (Action n) := prob.actions'.filter (fun a => applicable' a s)

    appli ≠ [] ∧ Option.some (h s) ≤ (appli.map (fun a => a.cost + h (successor' a s))).min?
  )

lemma weak_invariant_gives_le {n : ℕ} (prob : STRIPS n) (h : State' n → ℕ)
    (hi : weaker_than_perfect_heuristic_invariant prob h)
    (s : State' n) (hs : Nonempty (Plan prob (convertState s)))
    (a : Action n) (ha : a ∈ prob.actions') (happ : applicable' a s = true) :
    h s ≤ a.cost + h (successor' a s) := by
      have := hi s hs;
      rcases k : List.min? ( List.map ( fun a => a.cost + h ( successor' a s ) ) ( List.filter ( fun a => applicable' a s ) prob.actions' ) ) with ( _ | k ) <;> simp_all +decide;
      rw [ List.min?_eq_some_iff ] at k;
      split_ifs at this
      case pos hi =>
        grind
      case neg hi =>
        exact this.2.trans ( k.2 _ ( List.mem_map.mpr ⟨ a, List.mem_filter.mpr ⟨ ha, happ ⟩, rfl ⟩ ) )

/-- Auxiliary: path cost ≥ h(start) using weak invariant + goal-awareness. -/
private lemma path_cost_ge_heur_of_weak_invariant {n : ℕ} (prob : STRIPS n) (h : State' n → ℕ)
    (ga : heur_goal_aware prob h)
    (hi : weaker_than_perfect_heuristic_invariant prob h)
    (k : ℕ) {start : State' n} {goal : State n}
    (path : Path prob (convertState start) goal)
    (hlen : path.length ≤ k)
    (goal_state : prob.GoalState goal) :
    path.cost ≥ h start := by
  induction k generalizing start goal with
  | zero =>
    generalize hs : convertState start = s at path
    cases path with
    | empty =>
      simp [Path.cost]
      exact ga start (GoalState_implies_satisfies' prob start (hs ▸ goal_state))
    | cons => simp [Path.length] at hlen
  | succ k ih =>
    generalize hs : convertState start = s at path
    cases path with
    | empty =>
      simp [Path.cost]
      exact ga start (GoalState_implies_satisfies' prob start (hs ▸ goal_state))
    | cons a s2 ha succ path' =>
      subst hs
      haveI := successor_dec a (convertState start) s2 succ
      obtain ⟨s2', rfl⟩ := state_has_bitvec s2
      have a_app : applicable' a start = true := successor_implies_applicable succ
      have s2'_eq : s2' = successor' a start :=
        is_successor'_eq_successor' a start s2' (successor_implies_is_successor succ)
      subst s2'_eq
      have ih' := ih path' (by simp [Path.length] at hlen; exact hlen) goal_state
      have h_solvable : Nonempty (Plan prob (convertState start)) :=
        ⟨⟨goal, Path.cons a _ ha succ path', goal_state⟩⟩
      calc h start
          ≤ a.cost + h (successor' a start) :=
            weak_invariant_gives_le prob h hi start h_solvable a (mem_actions'_of_mem_actions ha) a_app
        _ ≤ a.cost + path'.cost := Nat.add_le_add_left ih' _
        _ = path'.cost + a.cost := Nat.add_comm _ _
        _ = (Path.cons a (convertState (successor' a start)) ha succ path').cost := by simp [Path.cost]

/-- The original statement is false without goal-awareness (same counterexample as above).
    We add `heur_goal_aware` as a hypothesis. -/
lemma admissible_of_weak_perfect_heuristic_invariant {n : ℕ} (prob : STRIPS n) (h : State' n → ℕ)
    (ga : heur_goal_aware prob h) :
  weaker_than_perfect_heuristic_invariant prob h → heur_admissible prob h := by
  intro hi v plan
  exact path_cost_ge_heur_of_weak_invariant prob h ga hi plan.path.length plan.path (le_refl _) plan.goal


def replace_goal {n : ℕ} (prob : STRIPS n) (new_goal : VarSet' n) : STRIPS n :=
  STRIPS.mk prob.varNames prob.actions' prob.init' new_goal
/-! ### Path last-step extraction for regression -/

/-- Any non-empty path ending at a goal state contains an action that is regressable
    through the goal. Proved by induction: the last action in the path produces the
    goal state and must therefore be regressable. -/
lemma path_has_regressable_action {n : ℕ} (prob : STRIPS n) (g : VarSet' n)
    {s1 s2 : State n} (path : Path (replace_goal prob g) s1 s2)
    (hgoal : (replace_goal prob g).GoalState s2)
    (hlen : 0 < path.length) :
    ∃ a ∈ prob.actions', regressable' a (state'_of_varset' g) = true := by
  induction path with
  | empty => exact absurd hlen (by unfold Path.length; omega)
  | cons a s_mid ha succ rest ih =>
    cases rest with
    | empty =>
      exact ⟨a, mem_actions'_of_mem_actions ha,
             successor_goal_implies_regressable a _ _ g succ hgoal⟩
    | cons b s_mid' hb succ' rest' =>
      exact ih hgoal (by show 0 < rest'.length + 1; omega)

/-- Removing the last action from a non-empty plan yields a prefix path whose
    endpoint satisfies the regressed goal condition. Additionally, the prefix path
    cost plus the last action cost equals the total path cost. -/
lemma plan_last_step_decomposition {n : ℕ} (prob : STRIPS n) (g : VarSet' n)
    {s : State' n} (plan : Plan (replace_goal prob g) (convertState s))
    (hng : ¬ satisfies' g s = true) :
    ∃ (a : Action n) (s_prev : State n) (prefix_path : Path (replace_goal prob g) (convertState s) s_prev),
      a ∈ prob.actions' ∧
      regressable' a (state'_of_varset' g) = true ∧
      Successor a s_prev plan.last ∧
      prefix_path.cost + a.cost = plan.path.cost ∧
      (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' g)))).GoalState s_prev := by
  rcases plan with ⟨last, path, goal⟩
  -- path is non-empty since s doesn't satisfy g
  cases path with
  | empty =>
    -- Empty path: convertState s = last, so s satisfies g, contradiction
    exact absurd (GoalState_implies_satisfies' _ s goal) hng
  | cons a s_mid ha succ rest =>
    -- Use cons_to_snoc to get snoc form with last action
    obtain ⟨s_prev, a_last, ha_last, prefix_path, succ_last, heq, _⟩ :=
      Path.cons_to_snoc ha succ rest
    refine ⟨a_last, s_prev, prefix_path, mem_actions'_of_mem_actions ha_last,
            successor_goal_implies_regressable a_last s_prev last g succ_last goal,
            succ_last, ?_, ?_⟩
    · -- Cost decomposition
      show prefix_path.cost + a_last.cost = (Path.cons a s_mid ha succ rest).cost
      rw [heq, Path.cost_snoc]
    · -- GoalState of s_prev for regressed goal
      exact predecessor_satisfies_regressed_goal a_last s_prev last g succ_last goal

/-
If a is regressable through g, then applying a to a state satisfying regress(a,g)
    gives a state satisfying g. This allows constructing a plan for prob_g from
    a plan for prob_{regress(a,g)} by appending action a.
-/
lemma apply_regressable_achieves_goal {n : ℕ} (a : Action n)
    (s_prev : State n) (g : VarSet' n)
    (happ : Applicable s_prev a)
    (hreg : regressable' a (state'_of_varset' g) = true)
    (hprev : convertVarSet (varset'_of_state' (regress' a (state'_of_varset' g))) ⊆ s_prev) :
    convertVarSet g ⊆ (s_prev \ a.del) ∪ a.add := by
      intro x hx;
      unfold regressable' at hreg; simp_all +decide [ List.mem_filter ] ;
      contrapose! hreg;
      use ⟨ x, by
        exact x.2 ⟩
      generalize_proofs at *;
      simp_all +decide [ convertVarSet, state'_of_varset'_getElem ];
      have hconvert : convertVarSet a.del' = a.del ∧ convertVarSet a.add' = a.add := by
        exact Prod.mk_inj.mp rfl
      simp_all +decide [ Finset.ext_iff, Set.ext_iff ];
      exact ⟨ by simpa [ convertVarSet ] using hconvert.1 x |>.2 ( hreg.1 ( hprev ( by
        unfold regress' at *; simp_all +decide [ convertVarSet ] ;
        unfold varset'_of_state' at *; simp_all +decide [ BitVec.getElem_ofBoolListLE ] ;
        exact Or.inr ( by rw [ state'_of_varset'_getElem ] ; aesop ) ) ) ), by simpa [ convertVarSet ] using hconvert.2 x |>.not.mpr hreg.2 ⟩

/-- Cast a path from one `replace_goal` problem to another (same actions). -/
noncomputable def cast_path_replace_goal {n : ℕ} (prob : STRIPS n) (g1 g2 : VarSet' n)
    {s1 s2 : State n} (path : Path (replace_goal prob g1) s1 s2) :
    Path (replace_goal prob g2) s1 s2 := by
  induction path with
  | empty s => exact Path.empty s
  | cons a s2 ha succ rest ih => exact Path.cons a s2 ha succ ih

lemma cast_path_replace_goal_cost {n : ℕ} (prob : STRIPS n) (g1 g2 : VarSet' n)
    {s1 s2 : State n} (path : Path (replace_goal prob g1) s1 s2) :
    (cast_path_replace_goal prob g1 g2 path).cost = path.cost := by
  induction path with
  | empty => rfl
  | cons a s2 ha succ rest ih =>
    unfold cast_path_replace_goal; simp only [Path.cost]; exact congrArg (· + a.cost) ih

lemma cast_path_replace_goal_length {n : ℕ} (prob : STRIPS n) (g1 g2 : VarSet' n)
    {s1 s2 : State n} (path : Path (replace_goal prob g1) s1 s2) :
    (cast_path_replace_goal prob g1 g2 path).length = path.length := by
  induction path with
  | empty => rfl
  | cons a s2 ha succ rest ih =>
    unfold cast_path_replace_goal; simp only [Path.length]; exact congrArg (· + 1) ih

/-
For a regressable action, h(prob_g)(s) ≤ a.cost + h(prob_{regress(a,g)})(s).
    Requires h to be perfect (not just invariant-satisfying) because we need
    optimal plan existence to construct the extended plan.
    The previous version with `perfect_heuristic_invariant` was too weak:
    the forward invariant allows h < opt due to zero-cost cycles, breaking
    the argument.
-/
lemma heur_le_regressable_action_cost {n : ℕ} (prob : STRIPS n)
    (h : STRIPS n → State' n → ℕ) (g : VarSet' n) (s : State' n)
    (hperf : ∀ g' : VarSet' n, heur_is_perfect (replace_goal prob g') (h (replace_goal prob g')))
    (hs : Nonempty (Plan (replace_goal prob g) (convertState s)))
    (a : Action n) (ha : a ∈ prob.actions')
    (hreg : regressable' a (state'_of_varset' g) = true) :
    h (replace_goal prob g) s ≤ a.cost + h (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' g)))) s := by
      by_cases h_solvable : Nonempty (Plan (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' g)))) (convertState s));
      · -- Let's obtain the optimal plan for the regressed goal.
        obtain ⟨plan_rg, hplan_rg⟩ := hperf (varset'_of_state' (regress' a (state'_of_varset' g))) |>.2.1 s h_solvable;
        obtain ⟨last_state, succ⟩ : ∃ last_state : State n, Successor a plan_rg.last last_state ∧ convertVarSet g ⊆ last_state := by
          have h_succ : Successor a plan_rg.last ((plan_rg.last \ a.del) ∪ a.add) := by
            have := plan_rg.goal; unfold STRIPS.GoalState at this; simp_all +decide [ Successor ] ;
            exact fun x hx => this <| by
              unfold replace_goal; simp_all +decide [ convertVarSet ] ;
              unfold regress' at *; simp_all +decide [ state'_of_varset', varset'_of_state' ] ;
              unfold regressable' at hreg; simp_all +decide [ Action.pre ] ;
              unfold convertVarSet at hx; simp_all +decide [ List.mem_map, List.mem_finRange ] ;
              rw [ BitVec.getElem_ofBoolListLE ] ; simp +decide [ hx ] ;
          generalize_proofs at *; (
          exact ⟨ _, h_succ, apply_regressable_achieves_goal a plan_rg.last g h_succ.1 hreg plan_rg.goal ⟩)
        generalize_proofs at *; (
        -- Construct the new plan by extending the plan for the regressed goal with the action a.
        obtain ⟨plan_g, hplan_g⟩ : ∃ plan_g : Plan (replace_goal prob g) (convertState s), plan_g.path.cost = plan_rg.path.cost + a.cost := by
          have hplan_g : ∃ plan_g : Path (replace_goal prob g) (convertState s) last_state, plan_g.cost = plan_rg.path.cost + a.cost := by
            use Path.snoc a plan_rg.last (by
            exact List.mem_toFinset.mpr ha) (cast_path_replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' g))) g plan_rg.path) (by
            exact succ.1)
            generalize_proofs at *; (
            grind +suggestions)
          generalize_proofs at *; (
          exact ⟨ ⟨ last_state, hplan_g.choose, succ.2 ⟩, hplan_g.choose_spec ⟩)
        generalize_proofs at *; (
        have := hperf g |>.1;
        grind));
      · have := hperf ( varset'_of_state' ( regress' a ( state'_of_varset' g ) ) ) |>.2.2 s ( by simpa using h_solvable ) ; simp_all +decide [ Nat.mul_comm ] ;
        refine' le_trans _ ( Nat.le_add_left _ _ ) |> le_trans <| Nat.add_le_add_left this _;
        convert perfect_heur_solvable_le_bound ( replace_goal prob g ) ( h ( replace_goal prob g ) ) ( hperf _ _ ) s hs using 1

/-
For the optimal plan from s to g, the last action a₀ achieves equality:
    h(prob_g)(s) = a₀.cost + h(prob_{regress(a₀,g)})(s).
    Requires h to be perfect to access optimal plans.
-/
lemma heur_eq_last_action_cost {n : ℕ} (prob : STRIPS n)
    (h : STRIPS n → State' n → ℕ) (g : VarSet' n) (s : State' n)
    (hperf : ∀ g' : VarSet' n, heur_is_perfect (replace_goal prob g') (h (replace_goal prob g')))
    (hs : Nonempty (Plan (replace_goal prob g) (convertState s)))
    (hng : ¬ satisfies' g s = true) :
    ∃ a ∈ prob.actions'.filter (fun a => regressable' a (state'_of_varset' g)),
      a.cost + h (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' g)))) s =
        h (replace_goal prob g) s := by
          -- By hperf for goal g, there exists an optimal plan plan_g from s to g with plan_g.path.cost = h(g)(s).
          obtain ⟨plan_g, hplan_g⟩ : ∃ plan_g : Plan (replace_goal prob g) (convertState s), plan_g.path.cost = h (replace_goal prob g) s := by
            specialize hperf g;
            exact hperf.2.1 s hs;
          -- Use plan_last_step_decomposition to decompose plan_g.
          obtain ⟨a, s_prev, prefix_path, ha, hreg, h_succ, h_cost, h_goal⟩ : ∃ a ∈ prob.actions', ∃ s_prev : State n, ∃ prefix_path : Path (replace_goal prob g) (convertState s) s_prev,
            regressable' a (state'_of_varset' g) = true ∧
            Successor a s_prev plan_g.last ∧
            prefix_path.cost + a.cost = plan_g.path.cost ∧
            (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' g)))).GoalState s_prev := by
              have := plan_last_step_decomposition prob g plan_g hng; aesop;
          have h_admissible : h (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' g)))) s ≤ ha.cost := by
            have h_admissible : ∀ (path : Path (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' g))) ) (convertState s) prefix_path), path.cost ≥ h (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' g))) ) s := by
              intros path
              apply (hperf (varset'_of_state' (regress' a (state'_of_varset' g)))).left s ⟨prefix_path, path, h_goal⟩;
            exact h_admissible ( cast_path_replace_goal prob g ( varset'_of_state' ( regress' a ( state'_of_varset' g ) ) ) ha ) |> le_trans <| by simp +decide [ cast_path_replace_goal_cost ] ;
          have h_eq : h (replace_goal prob g) s ≤ a.cost + h (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' g)))) s := by
            exact heur_le_regressable_action_cost prob h g s hperf hs a s_prev hreg
          grind

def perfect_heuristic_regression_invariant {n : ℕ} (prob : STRIPS n) (h : STRIPS n → State' n → ℕ):=
  ∀ s : State' n, ∀ g : VarSet' n,(
    Nonempty (Plan (replace_goal prob g) (convertState s)) → (
      -- consider any potential goal
      if satisfies' g s then h (replace_goal prob g) s = 0
      else
      (
        let regressi : List (Action n) := prob.actions'.filter (fun a => regressable' a (state'_of_varset' g))
        regressi ≠ [] ∧ Option.some (h (replace_goal prob g) s) =
          (regressi.map (fun a => a.cost + h (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' g)))) s)).min?
    )
  )) ∧
    (IsEmpty (Plan (replace_goal prob g) (convertState s)) → (h (replace_goal prob g) s) ≥ (2^n) * (max_action_cost prob))


/-- If h is perfect for all goals, then it satisfies the regression invariant.
    Note: the previous version used `perfect_heuristic_invariant` as hypothesis,
    which is strictly weaker and insufficient. -/
lemma perfect_regression_invar_of_is_perfect {n : ℕ} (prob : STRIPS n)
    (h : STRIPS n → State' n → ℕ) :
    (∀ g : VarSet' n, heur_is_perfect (replace_goal prob g) (h (replace_goal prob g))) →
      perfect_heuristic_regression_invariant prob h := by
  intro hperf _s _hs
  have _hinv : ∀ g : VarSet' n, perfect_heuristic_invariant (replace_goal prob g) (h (replace_goal prob g)) :=
    fun g => perfect_heuristic_has_invariant _ _ (hperf g)
  constructor
  · intro _g
    split_ifs
    case pos hsat =>
      specialize _hinv _hs
      obtain ⟨_hinv, _ ⟩ := _hinv
      specialize _hinv _s _g
      have : satisfies' (replace_goal prob _hs).goal' _s := by
        unfold replace_goal
        simp [hsat]
      simp [this] at _hinv
      exact _hinv
    · constructor
      · -- The plan has positive length (since _s doesn't satisfy the goal)
        obtain ⟨plan⟩ := _g
        have hlen : 0 < plan.path.length := by
          rcases plan with ⟨last, path, goal⟩
          cases path with
          | empty => exact absurd (GoalState_implies_satisfies' _ _s goal) ‹_›
          | cons => show 0 < _ + 1; omega
        obtain ⟨a, ha_mem, ha_reg⟩ := path_has_regressable_action prob _hs plan.path plan.goal hlen
        exact List.ne_nil_of_mem (List.mem_filter.mpr ⟨ha_mem, ha_reg⟩)
      · -- Use the two helper lemmas to establish the min? equation
        rw [eq_comm, List.min?_eq_some_iff]
        constructor
        · -- h(prob_g)(s) is achieved by some regressable action
          obtain ⟨a, ha_mem, ha_eq⟩ := heur_eq_last_action_cost prob h _hs _s hperf _g ‹_›
          rw [← ha_eq]
          exact List.mem_map.mpr ⟨a, ha_mem, rfl⟩
        · -- h(prob_g)(s) ≤ every element
          intro x hx
          rw [List.mem_map] at hx
          obtain ⟨a, ha_mem, rfl⟩ := hx
          rw [List.mem_filter] at ha_mem
          exact heur_le_regressable_action_cost prob h _hs _s hperf _g a ha_mem.1 ha_mem.2
  · intro isEmpty
    exact (hperf _hs).2.2 _s isEmpty

/-
From the regression invariant, extract the inequality h(g)(s) ≤ a.cost + h(regress(a,g))(s)
    for any regressable action a when s is solvable and doesn't satisfy g.
-/
lemma regression_invariant_le {n : ℕ} (prob : STRIPS n)
    (h : STRIPS n → State' n → ℕ)
    (hinv : perfect_heuristic_regression_invariant prob h)
    (g : VarSet' n) (s : State' n)
    (hs : Nonempty (Plan (replace_goal prob g) (convertState s)))
    (hng : ¬ satisfies' g s = true)
    (a : Action n) (ha : a ∈ prob.actions')
    (hreg : regressable' a (state'_of_varset' g) = true) :
    h (replace_goal prob g) s ≤ a.cost + h (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' g)))) s := by
      contrapose! hinv;
      intro H;
      have := H s g;
      simp_all 
      rw [ eq_comm, List.min?_eq_some_iff ] at this;
      exact not_lt_of_ge ( this.2.2 _ ( List.mem_map.mpr ⟨ a, List.mem_filter.mpr ⟨ ha, hreg ⟩, rfl ⟩ ) ) hinv

/-
Goal-awareness from the regression invariant.
-/
lemma goal_aware_of_regression_invariant {n : ℕ} (prob : STRIPS n)
    (h : STRIPS n → State' n → ℕ)
    (hinv : perfect_heuristic_regression_invariant prob h)
    (g : VarSet' n) (s : State' n)
    (hsat : satisfies' g s = true) :
    h (replace_goal prob g) s = 0 := by
      have := ( hinv s g );
      convert this.1 ?_;
      · grobner;
      · refine' ⟨ ⟨ _, _, _ ⟩ ⟩;
        exact convertState s;
        · exact Path.empty _;
        · exact satisfies'_implies_GoalState (replace_goal prob g) s hsat

/-- Auxiliary lemma: plan cost ≥ h for the regression invariant, by induction on plan length.
    Quantified over ALL goals simultaneously so the IH applies to regressed goals. -/
private lemma plan_cost_ge_heur_of_regression_aux {n : ℕ} (prob : STRIPS n)
    (h : STRIPS n → State' n → ℕ)
    (hinv : perfect_heuristic_regression_invariant prob h)
    (k : ℕ) (g : VarSet' n) {start : State' n} {goal : State n}
    (path : Path (replace_goal prob g) (convertState start) goal)
    (hlen : path.length ≤ k)
    (goal_state : (replace_goal prob g).GoalState goal) :
    path.cost ≥ h (replace_goal prob g) start := by
  induction k generalizing g start goal with
  | zero =>
    generalize hs : convertState start = s at path
    cases path with
    | empty =>
      simp [Path.cost]
      exact goal_aware_of_regression_invariant prob h hinv g start
        (GoalState_implies_satisfies' _ start (hs ▸ goal_state))
    | cons => simp [Path.length] at hlen
  | succ k ih =>
    generalize hs : convertState start = s at path
    cases path with
    | empty =>
      simp [Path.cost]
      exact goal_aware_of_regression_invariant prob h hinv g start
        (GoalState_implies_satisfies' _ start (hs ▸ goal_state))
    | cons a s_mid ha succ rest =>
      subst hs
      -- Build a plan for s to show solvability
      have h_solvable : Nonempty (Plan (replace_goal prob g) (convertState start)) :=
        ⟨⟨goal, Path.cons a s_mid ha succ rest, goal_state⟩⟩
      by_cases hsat : satisfies' g start = true
      · -- start satisfies g: h = 0
        have := goal_aware_of_regression_invariant prob h hinv g start hsat
        simp [this]
      · -- start doesn't satisfy g: decompose plan from end using cons_to_snoc
        have hng : ¬ satisfies' g start = true := hsat
        -- cons_to_snoc gives snoc decomposition with length equality
        obtain ⟨s_prev, a_last, ha_last, prefix_path, succ_last, hpath_eq, hlen_eq⟩ :=
          Path.cons_to_snoc ha succ rest
        -- The snoc form means a_last is the last action, prefix_path goes from start to s_prev
        -- and s_prev --a_last--> goal
        have ha_last_mem : a_last ∈ prob.actions' := mem_actions'_of_mem_actions ha_last
        have hreg_last := successor_goal_implies_regressable a_last s_prev goal g succ_last goal_state
        have hgoal_prev := predecessor_satisfies_regressed_goal a_last s_prev goal g succ_last goal_state
        -- Cast prefix to regressed goal problem
        set rg := varset'_of_state' (regress' a_last (state'_of_varset' g))
        -- Prefix length ≤ k (since rest.length = prefix_path.length and rest.length + 1 ≤ k + 1)
        have hprefix_len : prefix_path.length ≤ k := by
          simp [Path.length] at hlen; omega
        have ih_result := ih rg (cast_path_replace_goal prob g rg prefix_path) (by
          simp [cast_path_replace_goal_length]; exact hprefix_len) hgoal_prev
        -- Use regression_invariant_le
        have h_le := regression_invariant_le prob h hinv g start h_solvable hng
          a_last ha_last_mem hreg_last
        -- Cost equality: path cost = prefix cost + a_last cost (from snoc decomposition)
        have hcost : (Path.cons a s_mid ha succ rest).cost = prefix_path.cost + a_last.cost := by
          rw [hpath_eq]; exact Path.cost_snoc
        -- Combine
        have ih_cost : h (replace_goal prob rg) start ≤ prefix_path.cost := by
          calc h (replace_goal prob rg) start
              ≤ (cast_path_replace_goal prob g rg prefix_path).cost := ih_result
            _ = prefix_path.cost := cast_path_replace_goal_cost prob g rg prefix_path
        calc h (replace_goal prob g) start
            ≤ a_last.cost + h (replace_goal prob rg) start := h_le
          _ ≤ a_last.cost + prefix_path.cost := Nat.add_le_add_left ih_cost _
          _ = prefix_path.cost + a_last.cost := Nat.add_comm _ _
          _ = (Path.cons a s_mid ha succ rest).cost := hcost.symm

/-- The regression invariant implies admissibility for all goals. -/
lemma admissible_of_regression_invariant {n : ℕ} (prob : STRIPS n)
    (h : STRIPS n → State' n → ℕ) :
    perfect_heuristic_regression_invariant prob h →
    (∀ g : VarSet' n, heur_admissible (replace_goal prob g) (h (replace_goal prob g))) := by
  intro hinv g v plan
  exact plan_cost_ge_heur_of_regression_aux prob h hinv plan.path.length g plan.path
    (le_refl _) plan.goal

/-!
### Note on `perfect_invar_of_perfect_regression_invar`

The statement
```
perfect_heuristic_regression_invariant prob h →
  (∀ g, perfect_heuristic_invariant (replace_goal prob g) (h (replace_goal prob g)))
```
is **false** in general. A counterexample exists with zero-cost regression self-loops:
if an action `a` has `a.pre' ⊆ g`, `a.add' ∩ g = ∅`, `a.del' ∩ g = ∅`, and `a.cost = 0`,
then `regress(a, g) = g`, creating a zero-cost self-loop in the regression Bellman equation.
This allows `h(g)(s)` to take any value ≤ opt in the regression invariant, while the
forward invariant may force a unique (larger) value.

The correct equivalence is:
`(∀ g, heur_is_perfect (replace_goal prob g) (h ...)) ↔ perfect_heuristic_regression_invariant prob h`
where `heur_is_perfect` additionally requires optimal plan existence.
-/




def weaker_than_perfect_heuristic_regression_invariant {n : ℕ} (prob : STRIPS n) (h : STRIPS n → State' n → ℕ):=
  ∀ s : State' n, ∀ g : VarSet' n,(
    Nonempty (Plan (replace_goal prob g) (convertState s)) → (
      -- consider any potential goal
      if satisfies' g s then h (replace_goal prob g) s = 0
      else
      (
        let regressi : List (Action n) := prob.actions'.filter (fun a => regressable' a (state'_of_varset' g))
        regressi ≠ [] ∧ Option.some (h (replace_goal prob g) s) ≤ -- actual heuristic value might be lower
          (regressi.map (fun a => a.cost + h (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' g)))) s)).min?
    )
  )) ∧
    (IsEmpty (Plan (replace_goal prob g) (convertState s)) → (h (replace_goal prob g) s) ≥ (2^n) * (max_action_cost prob))

/-
From the weaker regression invariant, extract the key inequality: h(g,s) ≤ a.cost + h(regress(a,g), s).
-/
lemma weaker_regression_invariant_le {n : ℕ} (prob : STRIPS n)
    (h : STRIPS n → State' n → ℕ)
    (hinv : weaker_than_perfect_heuristic_regression_invariant prob h)
    (g : VarSet' n) (s : State' n)
    (hs : Nonempty (Plan (replace_goal prob g) (convertState s)))
    (hng : ¬ satisfies' g s = true)
    (a : Action n) (ha : a ∈ prob.actions')
    (hreg : regressable' a (state'_of_varset' g) = true) :
    h (replace_goal prob g) s ≤ a.cost + h (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' g)))) s := by
  contrapose! hinv;
  intro H;
  obtain ⟨regressi, hregressi⟩ : ∃ regressi : List (Action n), regressi = prob.actions'.filter (fun a => regressable' a (state'_of_varset' g)) ∧ Option.some (h (replace_goal prob g) s) ≤ (regressi.map (fun a => a.cost + h (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' g)))) s)).min? := by
    have := H s g; aesop;
  have h_min_le : ∀ {l : List ℕ}, l ≠ [] → ∀ x ∈ l, (List.min? l).getD 0 ≤ x := by
    exact fun {l} a x a_1 => List.min?_getD_le_of_mem a_1
  specialize h_min_le ( show List.map ( fun a => a.cost + h ( replace_goal prob ( varset'_of_state' ( regress' a ( state'_of_varset' g ) ) ) ) s ) regressi ≠ [ ] from ?_ ) ( a.cost + h ( replace_goal prob ( varset'_of_state' ( regress' a ( state'_of_varset' g ) ) ) ) s ) ?_ <;> simp_all +decide;
  · exact ⟨ a, ha, hreg ⟩;
  · exact ⟨ a, ⟨ ha, hreg ⟩, rfl ⟩;
  · cases h : List.min? ( List.map ( fun a => a.cost + h ( replace_goal prob ( varset'_of_state' ( regress' a ( state'_of_varset' g ) ) ) ) s ) ( List.filter ( fun a => regressable' a ( state'_of_varset' g ) ) prob.actions' ) ) <;> simp_all +decide;
    grind

/-
Goal-awareness from the weaker regression invariant.
-/
lemma goal_aware_of_weaker_regression_invariant {n : ℕ} (prob : STRIPS n)
    (h : STRIPS n → State' n → ℕ)
    (hinv : weaker_than_perfect_heuristic_regression_invariant prob h)
    (g : VarSet' n) (s : State' n)
    (hsat : satisfies' g s = true) :
    h (replace_goal prob g) s = 0 := by
  convert hinv s g |>.1 _ using 1;
  · lia;
  · refine' ⟨ ⟨ convertState s, Path.empty _, _ ⟩ ⟩;
    exact satisfies'_implies_GoalState (replace_goal prob g) s hsat

/-- Auxiliary: plan cost ≥ h for the weaker regression invariant, by induction on plan length. -/
private lemma plan_cost_ge_heur_of_weaker_regression_aux {n : ℕ} (prob : STRIPS n)
    (h : STRIPS n → State' n → ℕ)
    (hinv : weaker_than_perfect_heuristic_regression_invariant prob h)
    (k : ℕ) (g : VarSet' n) {start : State' n} {goal : State n}
    (path : Path (replace_goal prob g) (convertState start) goal)
    (hlen : path.length ≤ k)
    (goal_state : (replace_goal prob g).GoalState goal) :
    path.cost ≥ h (replace_goal prob g) start := by
  induction k generalizing g start goal with
  | zero =>
    generalize hs : convertState start = s at path
    cases path with
    | empty =>
      simp [Path.cost]
      exact goal_aware_of_weaker_regression_invariant prob h hinv g start
        (GoalState_implies_satisfies' _ start (hs ▸ goal_state))
    | cons => simp [Path.length] at hlen
  | succ k ih =>
    generalize hs : convertState start = s at path
    cases path with
    | empty =>
      simp [Path.cost]
      exact goal_aware_of_weaker_regression_invariant prob h hinv g start
        (GoalState_implies_satisfies' _ start (hs ▸ goal_state))
    | cons a s_mid ha succ rest =>
      subst hs
      have h_solvable : Nonempty (Plan (replace_goal prob g) (convertState start)) :=
        ⟨⟨goal, Path.cons a s_mid ha succ rest, goal_state⟩⟩
      by_cases hsat : satisfies' g start = true
      · have := goal_aware_of_weaker_regression_invariant prob h hinv g start hsat
        simp [this]
      · obtain ⟨s_prev, a_last, ha_last, prefix_path, succ_last, hpath_eq, hlen_eq⟩ :=
          Path.cons_to_snoc ha succ rest
        have ha_last_mem : a_last ∈ prob.actions' := mem_actions'_of_mem_actions ha_last
        have hreg_last := successor_goal_implies_regressable a_last s_prev goal g succ_last goal_state
        have hgoal_prev := predecessor_satisfies_regressed_goal a_last s_prev goal g succ_last goal_state
        set rg := varset'_of_state' (regress' a_last (state'_of_varset' g))
        have hprefix_len : prefix_path.length ≤ k := by
          simp [Path.length] at hlen; omega
        have ih_result := ih rg (cast_path_replace_goal prob g rg prefix_path) (by
          simp [cast_path_replace_goal_length]; exact hprefix_len) hgoal_prev
        have h_le := weaker_regression_invariant_le prob h hinv g start h_solvable hsat
          a_last ha_last_mem hreg_last
        have hcost : (Path.cons a s_mid ha succ rest).cost = prefix_path.cost + a_last.cost := by
          rw [hpath_eq]; exact Path.cost_snoc
        have ih_cost : h (replace_goal prob rg) start ≤ prefix_path.cost := by
          calc h (replace_goal prob rg) start
              ≤ (cast_path_replace_goal prob g rg prefix_path).cost := ih_result
            _ = prefix_path.cost := cast_path_replace_goal_cost prob g rg prefix_path
        calc h (replace_goal prob g) start
            ≤ a_last.cost + h (replace_goal prob rg) start := h_le
          _ ≤ a_last.cost + prefix_path.cost := Nat.add_le_add_left ih_cost _
          _ = prefix_path.cost + a_last.cost := Nat.add_comm _ _
          _ = (Path.cons a s_mid ha succ rest).cost := hcost.symm

---- weaker_than_perfect_heuristic_regression_invariant requires same bellman-style equation, but now with a ≤ instead of a =. Thus we should have pointwise domination, but only on solvable states
--lemma perfect_regression_dominates_weaker_regression_invariant {n : ℕ} (prob : STRIPS n) (h h_weak : STRIPS n → State' n → ℕ):
--  perfect_heuristic_regression_invariant prob h ∧
--  weaker_than_perfect_heuristic_regression_invariant prob h_weak →
--    ∀ s : State' n, ∀ g : VarSet' n, Nonempty (Plan (replace_goal prob g) (convertState s)) → h (replace_goal prob g) s ≥ h_weak (replace_goal prob g) s := by
--  sorry



/-- The weaker regression invariant implies admissibility for all goals. -/
lemma admissible_of_weaker_regression_invariant {n : ℕ} (prob : STRIPS n)
    (h : STRIPS n → State' n → ℕ) :
    weaker_than_perfect_heuristic_regression_invariant prob h →
    (∀ g : VarSet' n, heur_admissible (replace_goal prob g) (h (replace_goal prob g))) := by
  intro hinv g v plan
  exact plan_cost_ge_heur_of_weaker_regression_aux prob h hinv plan.path.length g plan.path
    (le_refl _) plan.goal


def bellman_heuristic_regression_invariant {n : ℕ} (prob : STRIPS n) (h : STRIPS n → State' n → ℕ):=
∀ s : State' n, ∀ g : VarSet' n,
-- consider any potential goal
if satisfies' g s then h (replace_goal prob g) s = 0
else
let regressi : List (Action n) := prob.actions'.filter (fun a => regressable' a (state'_of_varset' g))
if r : regressi = [] then
h (replace_goal prob g) s = (2^n) * (max_action_cost prob)
else
let minCostPredecessor := (regressi.map (fun a => a.cost + h (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' g)))) s)).min (by simp_all)

if minCostPredecessor ≥ (2^n) * (max_action_cost prob) then -- if unsolvable then still unsolvable
h (replace_goal prob g) s = (2^n) * (max_action_cost prob)
else
h (replace_goal prob g) s ≤ minCostPredecessor

/-
From the bellman regression invariant, extract the key inequality: h(g,s) ≤ a.cost + h(regress(a,g), s)
    when g is not satisfied and the min regression cost is below threshold.
-/
lemma bellman_regression_invariant_le {n : ℕ} (prob : STRIPS n)
    (h : STRIPS n → State' n → ℕ)
    (hinv : bellman_heuristic_regression_invariant prob h)
    (g : VarSet' n) (s : State' n)
    (hng : ¬ satisfies' g s = true)
    (a : Action n) (ha : a ∈ prob.actions')
    (hreg : regressable' a (state'_of_varset' g) = true)
    (h_below_threshold : h (replace_goal prob g) s < (2^n) * (max_action_cost prob)) :
    h (replace_goal prob g) s ≤ a.cost + h (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' g)))) s := by
  have := hinv s g
  split_ifs at this <;> simp_all +decide only [List.mem_filter]
  split_ifs at this <;> try omega
  exact le_trans this (List.min_le_of_mem (List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨ha, hreg⟩, rfl⟩))

/-
Goal-awareness from the bellman regression invariant.
-/
lemma goal_aware_of_bellman_regression_invariant {n : ℕ} (prob : STRIPS n)
    (h : STRIPS n → State' n → ℕ)
    (hinv : bellman_heuristic_regression_invariant prob h)
    (g : VarSet' n) (s : State' n)
    (hsat : satisfies' g s = true) :
    h (replace_goal prob g) s = 0 := by
  have := hinv s g; aesop;

/-- Auxiliary: plan cost ≥ h for the bellman regression invariant, by induction on plan length. -/
private lemma plan_cost_ge_heur_of_bellman_regression_aux {n : ℕ} (prob : STRIPS n)
    (h : STRIPS n → State' n → ℕ)
    (hinv : bellman_heuristic_regression_invariant prob h)
    (k : ℕ) (g : VarSet' n) {start : State' n} {goal : State n}
    (path : Path (replace_goal prob g) (convertState start) goal)
    (hlen : path.length ≤ k)
    (goal_state : (replace_goal prob g).GoalState goal) :
    path.cost ≥ h (replace_goal prob g) start := by
  induction k generalizing g start goal with
  | zero =>
    generalize hs : convertState start = s at path
    cases path with
    | empty =>
      simp [Path.cost]
      exact goal_aware_of_bellman_regression_invariant prob h hinv g start
        (GoalState_implies_satisfies' _ start (hs ▸ goal_state))
    | cons => simp [Path.length] at hlen
  | succ k ih =>
    generalize hs : convertState start = s at path
    cases path with
    | empty =>
      simp [Path.cost]
      exact goal_aware_of_bellman_regression_invariant prob h hinv g start
        (GoalState_implies_satisfies' _ start (hs ▸ goal_state))
    | cons a s_mid ha succ rest =>
      subst hs
      by_cases hsat : satisfies' g start = true
      · have := goal_aware_of_bellman_regression_invariant prob h hinv g start hsat
        simp [this]
      · obtain ⟨s_prev, a_last, ha_last, prefix_path, succ_last, hpath_eq, hlen_eq⟩ :=
          Path.cons_to_snoc ha succ rest
        have ha_last_mem : a_last ∈ prob.actions' := mem_actions'_of_mem_actions ha_last
        have hreg_last := successor_goal_implies_regressable a_last s_prev goal g succ_last goal_state
        have hgoal_prev := predecessor_satisfies_regressed_goal a_last s_prev goal g succ_last goal_state
        set rg := varset'_of_state' (regress' a_last (state'_of_varset' g))
        have hprefix_len : prefix_path.length ≤ k := by
          simp [Path.length] at hlen; omega
        have ih_result := ih rg (cast_path_replace_goal prob g rg prefix_path) (by
          simp [cast_path_replace_goal_length]; exact hprefix_len) hgoal_prev
        have hcost : (Path.cons a s_mid ha succ rest).cost = prefix_path.cost + a_last.cost := by
          rw [hpath_eq]; exact Path.cost_snoc
        have ih_cost : h (replace_goal prob rg) start ≤ prefix_path.cost := by
          calc h (replace_goal prob rg) start
              ≤ (cast_path_replace_goal prob g rg prefix_path).cost := ih_result
            _ = prefix_path.cost := cast_path_replace_goal_cost prob g rg prefix_path
        -- Use the bellman invariant
        have h_bellman := hinv start g
        simp [hsat] at h_bellman
        -- regressi is not empty since a_last is regressable
        have h_in_regressi : a_last ∈ prob.actions'.filter (fun a => regressable' a (state'_of_varset' g)) :=
          List.mem_filter.mpr ⟨ha_last_mem, hreg_last⟩
        -- Split the bellman invariant into cases
        split_ifs at h_bellman with h_no_regress h_min_ge_threshold
        · -- regressi = [] case: impossible since a_last is regressable
          exact absurd hreg_last (by rw [h_no_regress a_last ha_last_mem]; decide)
        · -- min ≥ threshold case: h = threshold
          have h_min_le : (List.map (fun a => a.cost + h (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' g)))) start)
              (List.filter (fun a => regressable' a (state'_of_varset' g)) prob.actions')).min (by simp_all [List.ne_nil_of_mem h_in_regressi]) ≤
              a_last.cost + h (replace_goal prob rg) start :=
            List.min_le_of_mem (List.mem_map.mpr ⟨a_last, h_in_regressi, rfl⟩)
          calc h (replace_goal prob g) start
              = (2^n) * (max_action_cost prob) := h_bellman
            _ ≤ _ := h_min_ge_threshold
            _ ≤ a_last.cost + h (replace_goal prob rg) start := h_min_le
            _ ≤ a_last.cost + prefix_path.cost := Nat.add_le_add_left ih_cost _
            _ = prefix_path.cost + a_last.cost := Nat.add_comm _ _
            _ = (Path.cons a s_mid ha succ rest).cost := hcost.symm
        · -- min < threshold case: h ≤ min
          have h_min_le : (List.map (fun a => a.cost + h (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' g)))) start)
              (List.filter (fun a => regressable' a (state'_of_varset' g)) prob.actions')).min (by simp_all [List.ne_nil_of_mem h_in_regressi]) ≤
              a_last.cost + h (replace_goal prob rg) start :=
            List.min_le_of_mem (List.mem_map.mpr ⟨a_last, h_in_regressi, rfl⟩)
          calc h (replace_goal prob g) start
              ≤ _ := h_bellman
            _ ≤ a_last.cost + h (replace_goal prob rg) start := h_min_le
            _ ≤ a_last.cost + prefix_path.cost := Nat.add_le_add_left ih_cost _
            _ = prefix_path.cost + a_last.cost := Nat.add_comm _ _
            _ = (Path.cons a s_mid ha succ rest).cost := hcost.symm

/-- The bellman regression invariant implies admissibility for all goals. -/
lemma admissible_of_bellman_regression_invariant {n : ℕ} (prob : STRIPS n)
    (h : STRIPS n → State' n → ℕ) :
    bellman_heuristic_regression_invariant prob h →
    (∀ g : VarSet' n, heur_admissible (replace_goal prob g) (h (replace_goal prob g))) := by
  sorry



def h_1_heuristic_regression_invariant {n : ℕ} (prob : STRIPS n) (h : STRIPS n → State' n → ℕ):=
  ∀ s : State' n, ∀ g : VarSet' n,
      -- consider any potential goal
      if satisfies' g s then h (replace_goal prob g) s = 0
      else
        if g_at_least_two : g.1.length > 1 then
          h (replace_goal prob g) s ≤ (g.1.map (fun g' => h (replace_goal prob ⟨[g'], by simp [List.SortedLT, StrictMono]⟩) s)).max (by intro h2; simp_all)
        else
          let regressi : List (Action n) := prob.actions'.filter (fun a => regressable' a (state'_of_varset' g))
          if r : regressi = [] then
            h (replace_goal prob g) s = (2^n) * (max_action_cost prob)
          else
            let minCostPredecessor := (regressi.map (fun a => a.cost + h (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' g)))) s)).min (by simp_all)
            if minCostPredecessor ≥ (2^n) * (max_action_cost prob) then -- if unsolvable then still unsolvable
              h (replace_goal prob g) s = (2^n) * (max_action_cost prob)
            else
              h (replace_goal prob g) s ≤ minCostPredecessor

/-
The h_1 regression invariant implies the bellman regression invariant for single-atom goals.
-/
lemma h_1_implies_bellman_for_singletons {n : ℕ} (prob : STRIPS n)
    (h : STRIPS n → State' n → ℕ)
    (hinv : h_1_heuristic_regression_invariant prob h)
    (g : Fin n) (s : State' n) :
    (if satisfies' ⟨[g], by simp [List.SortedLT, StrictMono]⟩ s
     then h (replace_goal prob ⟨[g], by simp [List.SortedLT, StrictMono]⟩) s = 0
     else
       let regressi := prob.actions'.filter (fun a => regressable' a (state'_of_varset' ⟨[g], by simp [List.SortedLT, StrictMono]⟩))
       if r : regressi = [] then
         h (replace_goal prob ⟨[g], by simp [List.SortedLT, StrictMono]⟩) s ≥ (2^n) * (max_action_cost prob)
       else
         let minCostPredecessor := (regressi.map (fun a => a.cost + h (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' ⟨[g], by simp [List.SortedLT, StrictMono]⟩)))) s)).min (by simp_all)
         if minCostPredecessor ≥ (2^n) * (max_action_cost prob) then
           h (replace_goal prob ⟨[g], by simp [List.SortedLT, StrictMono]⟩) s ≥ (2^n) * (max_action_cost prob)
         else
           h (replace_goal prob ⟨[g], by simp [List.SortedLT, StrictMono]⟩) s ≤ minCostPredecessor) := by
  contrapose! hinv;
  unfold h_1_heuristic_regression_invariant;
  grind

/-
Any plan that achieves a conjunction of goals also achieves each individual goal atom.
-/
lemma plan_for_conjunction_gives_plan_for_atom {n : ℕ} (prob : STRIPS n)
    (g : VarSet' n) (g' : Fin n) (hg' : g' ∈ g.1)
    (s : State' n) (plan : Plan (replace_goal prob g) (convertState s)) :
    Nonempty (Plan (replace_goal prob ⟨[g'], by simp [List.SortedLT, StrictMono]⟩) (convertState s)) := by
  refine' ⟨ ⟨ _, _, _ ⟩ ⟩;
  exact plan.last;
  · exact cast_path_replace_goal prob g ⟨[g'], by simp [List.SortedLT, StrictMono]⟩ plan.path;
  · have := plan.goal; simp_all +decide [ replace_goal, STRIPS.GoalState ] ;
    exact fun x hx => this <| by simp_all +decide [ convertVarSet ] ;

/-- The h_1 regression invariant implies admissibility for all goals.
    For multi-atom goals: h ≤ max of single-atom values, each ≤ plan cost.
    For single-atom goals: bellman invariant applies directly. -/
lemma admissible_of_h_1_regression_invariant {n : ℕ} (prob : STRIPS n)
    (h : STRIPS n → State' n → ℕ) :
    h_1_heuristic_regression_invariant prob h →
    (∀ g : VarSet' n, heur_admissible (replace_goal prob g) (h (replace_goal prob g))) := by
  sorry


end Validator
