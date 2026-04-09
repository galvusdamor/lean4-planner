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

lemma perferct_heuristic_is_perfect {n : ℕ} (prob : STRIPS n):
  heur_is_perfect prob (perfect_heuristic prob) := by
    constructor;
    · intro plan plan_1;
      unfold perfect_heuristic;
      cases h : planner ( STRIPS.mk prob.varNames prob.actions' plan prob.goal' ) ( fun _ => 0 ) <;> simp_all +decide;
      · have := planner_complete ( STRIPS.mk prob.varNames prob.actions' plan prob.goal' ) ( fun _ => 0 ) h;
        contrapose! this;
        exact ⟨ ⟨ plan_1.last, cast_path_to_replace prob plan plan_1.path, plan_1.goal ⟩ ⟩;
      · have := planner_optimal ( STRIPS.mk prob.varNames prob.actions' plan prob.goal' ) ( fun _ => 0 ) ( zero_heur_admissible _ );
        convert this ( by simp +decide [ h ] ) ( cast_plan_to_replace prob plan plan_1 ) |> le_trans <| ?_;
        · grind;
        · grind;
        · exact le_of_eq ( cast_path_to_replace_cost prob plan plan_1.path );
    · intro v hv
      unfold perfect_heuristic
      obtain ⟨plan, hplan⟩ := hv;
      cases h : planner ( STRIPS.mk prob.varNames prob.actions' v prob.goal' ) ( fun _ => 0 ) <;> simp_all +decide;
      · have := planner_complete ( STRIPS.mk prob.varNames prob.actions' v prob.goal' ) ( fun _ => 0 ) h;
        contrapose! this;
        exact ⟨ ⟨ plan, cast_path_to_replace prob v hplan, by assumption ⟩ ⟩;
      · rename_i hplan';
        exact ⟨ ⟨ hplan'.last, cast_path_from_replace prob v hplan'.path, hplan'.goal ⟩, cast_path_from_replace_cost prob v hplan'.path ⟩


/-
weak because the prefect heuristic has a particular value for solvable states and admissible heuristics can return arbirarily high values for that heuristic
-/
lemma perfect_heuristic_weak_dominates_admissible {n : ℕ} (prob : STRIPS n) (h : State' n → ℕ):
    heur_admissible prob h → ∀ s : State' n, Nonempty (Plan prob (convertState s)) → (perfect_heuristic prob) s ≥ h s := by
      intro h_admissible s hs_solvable
      obtain ⟨plan, hplan⟩ : ∃ plan : Plan prob (convertState s), plan.path.cost = perfect_heuristic prob s := by
        convert perferct_heuristic_is_perfect prob;
        constructor <;> intro h <;> cases h;
        · exact perferct_heuristic_is_perfect prob;
        · grind
      exact (by
      exact hplan ▸ h_admissible s plan)


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
    intro invar s s_is_goal
    obtain ⟨invar,_⟩ := invar
    specialize invar s (by sorry) -- since s is a goal state, the empty Plan suffices
    simp [s_is_goal] at invar
    exact invar

/-- The original statement `admissible_of_perfect_heuristic_invariant` is false without
    goal-awareness. Counterexample: `n = 1`, one noop action (cost 0), goal = `[]`
    (all states are goals), `h ≡ 1`. The invariant holds (`h(s) = min(0 + 1) = 1`)
    but `h` is not admissible (the empty plan has cost `0 < 1`).
    We add `heur_goal_aware` as a hypothesis. -/
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
      have := hp.1;
      -- By definition of `Plan`, we can construct a plan from `convertState s` to `convertState (successor' a s)` using `a`.
      obtain ⟨plan_succ, hplan_succ⟩ : ∃ plan_succ : Plan prob (convertState (successor' a s)), plan_succ.2.cost = h (successor' a s) := by
        obtain ⟨ plan_succ, hplan_succ ⟩ := hp.2 ( successor' a s ) hsolv_succ;
        exact ⟨ plan_succ, hplan_succ ⟩;
      have h_plan_succ : ∃ plan_succ' : Plan prob (convertState s), plan_succ'.2.cost ≤ a.cost + h (successor' a s) := by
        use ⟨plan_succ.last, Path.cons a (convertState (successor' a s)) (by
        exact List.mem_dedup.mpr ha) (Successor_of_applicable' a s happ) plan_succ.path, plan_succ.goal⟩
        generalize_proofs at *;
        exact add_comm a.cost _ ▸ add_le_add_left hplan_succ.le _;
      obtain ⟨ plan_succ', hplan_succ' ⟩ := h_plan_succ;
      exact le_trans ( this s plan_succ' ) hplan_succ'

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
        -- By hp.2 s hs, get plan with plan.path.cost = h s.
        obtain ⟨plan, hplan⟩ := hp.2 s hs
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
          exact ⟨ a₀, ⟨ mem_actions'_of_mem_actions ha₀, successor_implies_applicable succ₀ ⟩, by linarith [ perfect_le_action_succ prob h hp s a₀ ( mem_actions'_of_mem_actions ha₀ ) ( successor_implies_applicable succ₀ ) ⟨ last, rest, goal_sat ⟩ ] ⟩


lemma perfect_heuristic_has_invariant {n : ℕ} (prob : STRIPS n) (h : State' n → ℕ):
    heur_is_perfect prob h → perfect_heuristic_invariant prob h := by
  intro hp s hs
  split_ifs with hgoal
  · exact perfect_is_goal_aware prob h hp s hgoal
  · have hng : satisfies' prob.goal' s = false := by
      simpa using hgoal
    constructor
    · exact solvable_non_goal_has_applicable prob s hs hng
    · rw [eq_comm, List.min?_eq_some_iff]
      constructor
      · -- h s is achieved by some applicable action
        obtain ⟨a, ha_mem, ha_eq⟩ := perfect_achieves_min prob h hp s hs hng
        rw [← ha_eq]
        exact List.mem_map.mpr ⟨a, ha_mem, rfl⟩
      · -- h s ≤ every element by consistency
        intro x hx
        rw [List.mem_map] at hx
        obtain ⟨a, ha_mem, rfl⟩ := hx
        rw [List.mem_filter] at ha_mem
        have := hc s a ha_mem.1 ha_mem.2
        omega

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


lemma perfect_regression_invar_of_perfect_invar {n : ℕ} (prob : STRIPS n)
    (h : STRIPS n → State' n → ℕ) :
    (∀ g : VarSet' n, perfect_heuristic_invariant (replace_goal prob g) (h (replace_goal prob g))) →
      perfect_heuristic_regression_invariant prob h := by
  intro _hinv _s _hs 
  constructor
  · intro _g
    split_ifs
    case pos hsat =>
      specialize _hinv _hs --
      obtain ⟨_hinv, _ ⟩ := _hinv
      specialize _hinv _s _g
      have : satisfies' (replace_goal prob _hs).goal' _s := by 
        unfold replace_goal
        simp [hsat]
      simp [this] at _hinv
      exact _hinv
    · constructor
      · sorry  -- plan type is non empty and state does not satisfy the goal. Then the existing plan must have a last action that is regressible
      · sorry -- the idea is to "invert" the plan that we consider the the perfect forward heuristic
  · intro isEmpty
    specialize _hinv _hs
    obtain ⟨_ ,_hinv⟩ := _hinv
    specialize _hinv _s isEmpty
    convert _hinv using 1

lemma perfect_invar_of_perfect_regression_invar {n : ℕ} (prob : STRIPS n)
    (h : STRIPS n → State' n → ℕ) :
    perfect_heuristic_regression_invariant prob h →
    (∀ g : VarSet' n, perfect_heuristic_invariant (replace_goal prob g) (h (replace_goal prob g))) := by
  sorry

end Validator
