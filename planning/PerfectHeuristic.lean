import planning.Planner

set_option maxHeartbeats 0

namespace STRIPS

/-! ### Casting plans between STRIPS problems with the same actions and goals -/

/-- Replace the initial state of a STRIPS problem. -/
def replace_init_state {n : ℕ} (prob : PlanningTask n) (s : BitVec n) : PlanningTask n :=
  PlanningTask.mk prob.varNames prob.actions' (varset'_of_state' s) prob.goal'

/-- Cast a path from `prob` to `replace_init_state prob s`. -/
noncomputable def cast_path_to_replace {n : ℕ} (prob : PlanningTask n) (s : BitVec n) {s1 s2 : State n}
    (path : PlanningTask.Path prob s1 s2) : PlanningTask.Path (replace_init_state prob s) s1 s2 := by
  induction path with
  | empty s => exact PlanningTask.Path.empty s
  | cons a s2 ha succ rest ih => exact PlanningTask.Path.cons a s2 ha succ ih

/-- Cast a path from `replace_init_state prob s` to `prob`. -/
noncomputable def cast_path_from_replace {n : ℕ} (prob : PlanningTask n) (s : BitVec n) {s1 s2 : State n}
    (path : PlanningTask.Path (replace_init_state prob s) s1 s2) : PlanningTask.Path prob s1 s2 := by
  induction path with
  | empty s => exact PlanningTask.Path.empty s
  | cons a s2 ha succ rest ih => exact PlanningTask.Path.cons a s2 ha succ ih

lemma cast_path_to_replace_cost {n : ℕ} (prob : PlanningTask n) (s : BitVec n) {s1 s2 : State n}
    (path : PlanningTask.Path prob s1 s2) : (cast_path_to_replace prob s path).cost = path.cost := by
  induction path with
  | empty => rfl
  | cons a s2 ha succ rest ih =>
    unfold cast_path_to_replace; simp only [PlanningTask.Path.cost]; exact congrArg (· + a.cost) ih

lemma cast_path_from_replace_cost {n : ℕ} (prob : PlanningTask n) (s : BitVec n) {s1 s2 : State n}
    (path : PlanningTask.Path (replace_init_state prob s) s1 s2) : (cast_path_from_replace prob s path).cost = path.cost := by
  induction path with
  | empty => rfl
  | cons a s2 ha succ rest ih =>
    unfold cast_path_from_replace; simp only [PlanningTask.Path.cost]; exact congrArg (· + a.cost) ih

/-- Cast a plan from `prob` to `replace_init_state prob s`. -/
noncomputable def cast_plan_to_replace {n : ℕ} (prob : PlanningTask n) (s : BitVec n)
    (plan : PlanningTask.Plan prob (convertState s)) : PlanningTask.Plan (replace_init_state prob s) (convertState s) :=
  ⟨plan.last, cast_path_to_replace prob s plan.path, plan.goal⟩

/-- Cast a plan from `replace_init_state prob s` to `prob`. -/
noncomputable def cast_plan_from_replace {n : ℕ} (prob : PlanningTask n) (s : BitVec n)
    (plan : PlanningTask.Plan (replace_init_state prob s) (convertState s)) : PlanningTask.Plan prob (convertState s) :=
  ⟨plan.last, cast_path_from_replace prob s plan.path, plan.goal⟩

lemma replace_init_state_init {n : ℕ} (prob : PlanningTask n) (s : BitVec n) :
    (replace_init_state prob s).init = convertState s := by
  ext i
  simp [replace_init_state, PlanningTask.init, convertState, varset'_of_state', VarSet.mem_iff]

/-! ### Perfect heuristic -/

def perfect_heuristic {n : ℕ} (prob : PlanningTask n) (s : BitVec n) : ℕ∞ :=
  let replace_init := PlanningTask.mk prob.varNames prob.actions' (varset'_of_state' s) prob.goal'
  let opt_ret := planner replace_init (fun _ => 0)
  match opt_ret with
  | .none => ⊤
  | .some ret =>
      (ret.2.cost : ℕ∞)

/-- When a state is unsolvable, the planner on the corresponding replaced problem returns none. -/
private lemma planner_none_of_unsolvable {n : ℕ} (prob : PlanningTask n) (v : BitVec n)
    (hv : IsEmpty (PlanningTask.Plan prob (convertState v))) :
    planner (replace_init_state prob v) (fun _ => 0) = none := by
  by_contra h_ne
  cases h : planner (replace_init_state prob v) (fun _ => 0) with
  | none => exact h_ne h
  | some ret => exact hv.false (cast_plan_from_replace prob v ret)

lemma perferct_heuristic_is_perfect {n : ℕ} (prob : PlanningTask n):
  heur_is_perfect prob (perfect_heuristic prob) := by
  refine' ⟨ _, _, _ ⟩;
  · intro v plan
    unfold perfect_heuristic
    cases h : planner ( PlanningTask.mk prob.varNames prob.actions' (varset'_of_state' v) prob.goal' ) ( fun _ => 0 ) <;> simp_all 
    · have := planner_complete ( PlanningTask.mk prob.varNames prob.actions' (varset'_of_state' v) prob.goal' ) ( fun _ => 0 ) ( zero_heur_admissible' ( PlanningTask.mk prob.varNames prob.actions' (varset'_of_state' v) prob.goal' ) ) h; exact this.false ( cast_plan_to_replace prob v plan )
    · have := planner_optimal (PlanningTask.mk prob.varNames prob.actions' (varset'_of_state' v) prob.goal') (fun _ => 0) (zero_heur_admissible _) (by rw [h]; simp) (cast_plan_to_replace prob v plan);
      convert this.le using 1
      · grind
      · exact cast_path_to_replace_cost prob v plan.path ▸ rfl
  · unfold perfect_heuristic
    intro v hv
    cases h : planner ( PlanningTask.mk prob.varNames prob.actions' (varset'_of_state' v) prob.goal' ) ( fun _ => 0 ) <;> simp_all
    · convert planner_complete _ _ _ h
      · constructor <;> intro h <;> contrapose! h
        · trivial
        · exact ⟨ hv.some |> fun p => ⟨ p.last, cast_path_to_replace prob v p.path, p.goal ⟩ ⟩;
      · exact fun goal _ p => by simp
    · exact ⟨ cast_plan_from_replace prob v ‹_›, by exact_mod_cast cast_path_from_replace_cost prob v _ ⟩;
  · intro v hv; unfold perfect_heuristic
    convert planner_none_of_unsolvable prob v hv using 1
    cases h : planner ( PlanningTask.mk prob.varNames prob.actions' (varset'_of_state' v) prob.goal' ) ( fun _ => 0 ) <;> simp [ h ]
    · exact h
    · exact h.symm ▸ by tauto

lemma perfect_heuristic_weak_dominates_admissible {n : ℕ} (prob : PlanningTask n) (h : BitVec n → ℕ∞):
    heur_admissible prob h → ∀ s : BitVec n, Nonempty (PlanningTask.Plan prob (convertState s)) → (perfect_heuristic prob) s ≥ h s := by
      intro h_admissible s hs_solvable
      obtain ⟨plan, hplan⟩ : ∃ plan : PlanningTask.Plan prob (convertState s), plan.path.cost = perfect_heuristic prob s := by
        convert perferct_heuristic_is_perfect prob
        constructor <;> intro h <;> cases h
        · exact perferct_heuristic_is_perfect prob
        · grind
      exact hplan ▸ h_admissible s plan


-- A perfect heuristic has for all solvable states that the heuristic value is determine by considering the "cheapest" applicable action and the heuristic of the successor
def perfect_heuristic_invariant {n : ℕ} (prob : PlanningTask n) (h : BitVec n → ℕ∞):=
  (∀ s : BitVec n, Nonempty (PlanningTask.Plan prob (convertState s)) →
  if satisfies' prob.goal' s  then h s = 0
  else
  (
    let appli : List (Action n) := prob.actions'.filter (fun a => applicable' a s)

    appli ≠ [] ∧ Option.some (h s) = (appli.map (fun a => a.cost + h (successor' a s))).min?
  ))
  ∧
  ∀ s : BitVec n, IsEmpty (PlanningTask.Plan prob (convertState s)) →
    h s = ⊤

/-! ### Helper: the invariant implies h(s) ≤ a.cost + h(succ(a,s)) -/

lemma invariant_gives_le {n : ℕ} (prob : PlanningTask n) (h : BitVec n → ℕ∞)
    (hi : perfect_heuristic_invariant prob h)
    (s : BitVec n) (hs : Nonempty (PlanningTask.Plan prob (convertState s)))
    (a : Action n) (ha : a ∈ prob.actions') (happ : applicable' a s = true) :
    h s ≤ a.cost + h (successor' a s) := by
  contrapose! hi;
  intro H;
  have h_min : Option.some (h s) = (prob.actions'.filter (fun a => applicable' a s) |>.map (fun a => a.cost + h (successor' a s))).min? := by
    have := H.1 s hs;
    split_ifs at this <;> simp_all +decide;
  rw [ eq_comm, List.min?_eq_some_iff ] at h_min;
  exact not_lt_of_ge ( h_min.2 _ ( List.mem_map.mpr ⟨ a, List.mem_filter.mpr ⟨ ha, happ ⟩, rfl ⟩ ) ) hi

private lemma path_cost_ge_heur_of_invariant {n : ℕ} (prob : PlanningTask n) (h : BitVec n → ℕ∞)
    (ga : heur_goal_aware prob h)
    (hi : perfect_heuristic_invariant prob h)
    (k : ℕ) {start : BitVec n} {goal : State n}
    (path : PlanningTask.Path prob (convertState start) goal)
    (hlen : path.length ≤ k)
    (goal_state : prob.GoalState goal) :
    path.cost ≥ h start := by
  induction k generalizing start goal with
  | zero =>
    generalize hs : convertState start = s at path
    cases path with
    | empty =>
      have := ga start (GoalState_implies_satisfies' prob start (hs ▸ goal_state))
      simp [PlanningTask.Path.cost, this]
    | cons => simp [PlanningTask.Path.length] at hlen
  | succ k ih =>
    generalize hs : convertState start = s at path
    cases path with
    | empty =>
      have := ga start (GoalState_implies_satisfies' prob start (hs ▸ goal_state))
      simp [PlanningTask.Path.cost, this]
    | cons a s2 ha succ path' =>
      subst hs
      haveI := successor_dec a (convertState start) s2 succ
      obtain ⟨s2', rfl⟩ := state_has_bitvec s2
      have a_app : applicable' a start = true := successor_implies_applicable succ
      have s2'_eq : s2' = successor' a start :=
        is_successor'_eq_successor' a start s2' (successor_implies_is_successor succ)
      subst s2'_eq
      have ih' := ih path' (by simp [PlanningTask.Path.length] at hlen; exact hlen) goal_state
      have h_solvable : Nonempty (PlanningTask.Plan prob (convertState start)) :=
        ⟨⟨goal, PlanningTask.Path.cons a _ ha succ path', goal_state⟩⟩
      calc h start
          ≤ (a.cost : ℕ∞) + h (successor' a start) :=
            invariant_gives_le prob h hi start h_solvable a (mem_actions'_of_mem_actions ha) a_app
        _ ≤ (a.cost : ℕ∞) + (path'.cost : ℕ∞) := by gcongr
        _ = ((PlanningTask.Path.cons a (convertState (successor' a start)) ha succ path').cost : ℕ∞) := by
              simp [PlanningTask.Path.cost]; ring


lemma goal_aware_of_perfect_heuristic_invariant {n : ℕ} (prob : PlanningTask n) (h : BitVec n → ℕ∞):
  perfect_heuristic_invariant prob h → heur_goal_aware prob h := by
    intro ⟨invar, _⟩ s s_is_goal
    have goal_state := satisfies'_implies_GoalState prob s s_is_goal
    have hs : Nonempty (PlanningTask.Plan prob (convertState s)) :=
      ⟨⟨convertState s, PlanningTask.Path.empty _, goal_state⟩⟩
    specialize invar s hs
    simp [s_is_goal] at invar
    exact invar

lemma admissible_of_perfect_heuristic_invariant {n : ℕ} (prob : PlanningTask n) (h : BitVec n → ℕ∞):
  perfect_heuristic_invariant prob h → heur_admissible prob h := by
  intro hi v plan
  exact path_cost_ge_heur_of_invariant prob h (goal_aware_of_perfect_heuristic_invariant prob h hi) hi plan.path.length plan.path (le_refl _) plan.goal

/-! ### Helper lemmas for perfect_heuristic_has_invariant -/

/-
A perfect heuristic is goal-aware: h(s) = 0 when s satisfies the goal.
-/
lemma perfect_is_goal_aware {n : ℕ} (prob : PlanningTask n) (h : BitVec n → ℕ∞)
    (hp : heur_is_perfect prob h) (s : BitVec n)
    (hsat : satisfies' prob.goal' s = true) : h s = 0 := by
  obtain ⟨ _, _, _ ⟩ := hp;
  obtain ⟨ plan, hplan ⟩ := ‹∀ v : BitVec n, Nonempty ( PlanningTask.Plan prob ( convertState v ) ) → ∃ plan : PlanningTask.Plan prob ( convertState v ), ↑plan.path.cost = h v› s ⟨ convertState s, PlanningTask.Path.empty _, satisfies'_implies_GoalState prob s hsat ⟩;
  have := ‹heur_admissible prob h› s ⟨ convertState s, PlanningTask.Path.empty _, satisfies'_implies_GoalState prob s hsat ⟩ ; simp_all +decide [ PlanningTask.Path.cost ] ;

lemma Successor_of_applicable' {n : ℕ} (a : Action n) (s : BitVec n)
    (happ : applicable' a s = true) :
    Successor a (convertState s) (convertState (successor' a s)) := by
  refine ⟨fun i hi => (applicable'_iff a s).mp happ i (Action.mem_pre.mp hi), ?_⟩
  apply Set.ext
  intro i
  simp [convertState, successor', VarSet.mem_iff]

lemma solvable_non_goal_has_applicable {n : ℕ} (prob : PlanningTask n) (s : BitVec n)
    (hs : Nonempty (PlanningTask.Plan prob (convertState s)))
    (hng : satisfies' prob.goal' s = false) :
    (prob.actions'.filter (fun a => applicable' a s)) ≠ [] := by
  by_contra h_empty;
  have h_unsolvable : IsEmpty (PlanningTask.Plan prob (convertState s)) := by
    constructor;
    rintro ⟨ goal, path, hgoal ⟩;
    rcases path with ( _ | ⟨ a, s', ha, succ, path ⟩ ) <;> simp_all 
    · exact absurd ( GoalState_implies_satisfies' prob s hgoal ) ( by aesop );
    ·
      -- Apply the hypothesis `h_empty` to the action `a` and the fact that `a` is in the actions' list.
      have := h_empty a (mem_actions'_of_mem_actions ha); simp_all +decide [ Successor ];
      -- Apply the hypothesis `h_empty` to the action `a` and the fact that `a` is in the actions' list to conclude that `a` is not applicable in `s`.
      apply absurd (succ.left) (by
      convert this using 1;
      simp +decide [ applicable' ];
      simp +decide [ satisfies', Set.subset_def ])
  exact h_unsolvable.elim hs.some

lemma perfect_le_action_succ {n : ℕ} (prob : PlanningTask n) (h : BitVec n → ℕ∞)
    (hp : heur_is_perfect prob h) (s : BitVec n)
    (a : Action n) (ha : a ∈ prob.actions')
    (happ : applicable' a s = true)
    (hsolv_succ : Nonempty (PlanningTask.Plan prob (convertState (successor' a s)))) :
    h s ≤ a.cost + h (successor' a s) := by
  obtain ⟨plan_succ, hplan_succ⟩ := hp.2.1 (successor' a s) hsolv_succ;
  have := hp.1 s (PlanningTask.Plan.mk plan_succ.last (PlanningTask.Path.cons a (convertState (successor' a s)) (List.mem_dedup.mpr ha) (Successor_of_applicable' a s happ) plan_succ.path) plan_succ.goal);
  convert this using 1;
  rw [ ← hplan_succ ];
  exact mod_cast add_comm _ _

lemma perfect_achieves_min {n : ℕ} (prob : PlanningTask n) (h : BitVec n → ℕ∞)
    (hp : heur_is_perfect prob h) (s : BitVec n)
    (hs : Nonempty (PlanningTask.Plan prob (convertState s)))
    (hng : satisfies' prob.goal' s = false) :
    ∃ a ∈ prob.actions'.filter (fun a => applicable' a s),
      a.cost + h (successor' a s) = h s := by
  obtain ⟨ plan, hplan ⟩ := hp.2.1 s hs;
  rcases plan with ⟨ goal, path, hgoal ⟩ ; rcases path with ( _ | ⟨ a, s', ha, succ, path ⟩ ) <;> simp_all +decide [ PlanningTask.Path.cost ] ;
  · exact absurd ( GoalState_implies_satisfies' prob s hgoal ) ( by aesop );
  · have h_succ : s' = convertState (successor' a s) := by
      unfold successor';
      have := succ.right; simp_all +decide [ Fin.forall_iff, Set.ext_iff, VarSet.mem_iff ] ;
    have h_succ_solvable : Nonempty (PlanningTask.Plan prob (convertState (successor' a s))) := by
      exact ⟨ ⟨ goal, h_succ ▸ path, hgoal ⟩ ⟩;
    have h_succ_cost : h (successor' a s) ≤ path.cost := by
      convert hp.1 ( successor' a s ) ⟨ goal, path |> fun p => h_succ ▸ p, hgoal ⟩ using 1;
      grind;
    have h_succ_cost : h s ≤ a.cost + h (successor' a s) := by
      apply perfect_le_action_succ prob h hp s a (mem_actions'_of_mem_actions ha) (by
      exact successor_implies_applicable ( h_succ ▸ succ )) h_succ_solvable;
    have h_succ_cost : h s = a.cost + h (successor' a s) := by
      exact le_antisymm h_succ_cost ( by simpa [ add_comm, hplan.symm ] using add_le_add_left ‹h ( successor' a s ) ≤ ↑path.cost› ( a.cost : ℕ∞ ) );
    grind +suggestions

lemma perfect_le_action_succ_general {n : ℕ} (prob : PlanningTask n) (h : BitVec n → ℕ∞)
    (hp : heur_is_perfect prob h) (s : BitVec n)
    (hs : Nonempty (PlanningTask.Plan prob (convertState s)))
    (a : Action n) (ha : a ∈ prob.actions')
    (happ : applicable' a s = true) :
    h s ≤ a.cost + h (successor' a s) := by
  by_cases hsolv : Nonempty (PlanningTask.Plan prob (convertState (successor' a s)))
  · exact perfect_le_action_succ prob h hp s a ha happ hsolv
  · -- successor is unsolvable, so `h (successor' a s) = ⊤` and the bound is trivial
    rw [not_nonempty_iff] at hsolv
    have h_bound := hp.2.2 (successor' a s) hsolv
    simp [h_bound]

lemma perfect_heuristic_has_invariant {n : ℕ} (prob : PlanningTask n) (h : BitVec n → ℕ∞):
    heur_is_perfect prob h → perfect_heuristic_invariant prob h := by
  intro hp;
  refine' ⟨ fun s hs => _, fun s hs => _ ⟩;
  · by_cases hng : satisfies' prob.goal' s = false;
    · obtain ⟨ a, ha, hmin ⟩ := perfect_achieves_min prob h hp s hs hng;
      have h_min : ∀ a' ∈ prob.actions'.filter (fun a => applicable' a s), a'.cost + h (successor' a' s) ≥ h s := by
        grind +suggestions;
      have h_min : List.min? (List.map (fun a => a.cost + h (successor' a s)) (prob.actions'.filter (fun a => applicable' a s))) = some (h s) := by
        rw [ List.min?_eq_some_iff ];
        grind +revert;
      grind;
    · have := perfect_is_goal_aware prob h hp s ( by simpa using hng ) ; aesop;
  · exact hp.2.2 s hs

def weaker_than_perfect_heuristic_invariant {n : ℕ} (prob : PlanningTask n) (h : BitVec n → ℕ∞):=
  ∀ s : BitVec n, Nonempty (PlanningTask.Plan prob (convertState s)) →
  if satisfies' prob.goal' s  then h s = 0
  else
  (
    let appli : List (Action n) := prob.actions'.filter (fun a => applicable' a s)

    appli ≠ [] ∧ Option.some (h s) ≤ (appli.map (fun a => a.cost + h (successor' a s))).min?
  )

lemma weak_invariant_gives_le {n : ℕ} (prob : PlanningTask n) (h : BitVec n → ℕ∞)
    (hi : weaker_than_perfect_heuristic_invariant prob h)
    (s : BitVec n) (hs : Nonempty (PlanningTask.Plan prob (convertState s)))
    (a : Action n) (ha : a ∈ prob.actions') (happ : applicable' a s = true) :
    h s ≤ a.cost + h (successor' a s) := by
  convert hi s hs;
  split_ifs <;> simp_all 
  · have := hi s hs; simp_all +decide [ weaker_than_perfect_heuristic_invariant ] ;
  · constructor <;> intro h;
    · exact ⟨ ⟨ a, ha, happ ⟩, by simpa [ List.min?_eq_some_iff ] using hi s hs |> fun h => by aesop ⟩;
    · cases h : List.min? ( List.map ( fun a => ( a.cost : ℕ∞ ) + ‹BitVec n → ℕ∞› ( successor' a s ) ) ( List.filter ( fun a => applicable' a s ) prob.actions' ) ) <;> simp_all +decide [ List.min?_eq_some_iff ];
      exact le_trans ( by tauto ) ( h.2 _ _ ha happ rfl )

private lemma path_cost_ge_heur_of_weak_invariant {n : ℕ} (prob : PlanningTask n) (h : BitVec n → ℕ∞)
    (ga : heur_goal_aware prob h)
    (hi : weaker_than_perfect_heuristic_invariant prob h)
    (k : ℕ) {start : BitVec n} {goal : State n}
    (path : PlanningTask.Path prob (convertState start) goal)
    (hlen : path.length ≤ k)
    (goal_state : prob.GoalState goal) :
    path.cost ≥ h start := by
  induction k generalizing start goal with
  | zero =>
    generalize hs : convertState start = s at path
    cases path with
    | empty =>
      have := ga start (GoalState_implies_satisfies' prob start (hs ▸ goal_state))
      simp [PlanningTask.Path.cost, this]
    | cons => simp [PlanningTask.Path.length] at hlen
  | succ k ih =>
    generalize hs : convertState start = s at path
    cases path with
    | empty =>
      have := ga start (GoalState_implies_satisfies' prob start (hs ▸ goal_state))
      simp [PlanningTask.Path.cost, this]
    | cons a s2 ha succ path' =>
      subst hs
      haveI := successor_dec a (convertState start) s2 succ
      obtain ⟨s2', rfl⟩ := state_has_bitvec s2
      have a_app : applicable' a start = true := successor_implies_applicable succ
      have s2'_eq : s2' = successor' a start :=
        is_successor'_eq_successor' a start s2' (successor_implies_is_successor succ)
      subst s2'_eq
      have ih' := ih path' (by simp [PlanningTask.Path.length] at hlen; exact hlen) goal_state
      have h_solvable : Nonempty (PlanningTask.Plan prob (convertState start)) :=
        ⟨⟨goal, PlanningTask.Path.cons a _ ha succ path', goal_state⟩⟩
      calc h start
          ≤ (a.cost : ℕ∞) + h (successor' a start) :=
            weak_invariant_gives_le prob h hi start h_solvable a (mem_actions'_of_mem_actions ha) a_app
        _ ≤ (a.cost : ℕ∞) + (path'.cost : ℕ∞) := by gcongr
        _ = ((PlanningTask.Path.cons a (convertState (successor' a start)) ha succ path').cost : ℕ∞) := by
              simp [PlanningTask.Path.cost]; ring
lemma admissible_of_weak_perfect_heuristic_invariant {n : ℕ} (prob : PlanningTask n) (h : BitVec n → ℕ∞)
    (ga : heur_goal_aware prob h) :
  weaker_than_perfect_heuristic_invariant prob h → heur_admissible prob h := by
  intro hi v plan
  exact path_cost_ge_heur_of_weak_invariant prob h ga hi plan.path.length plan.path (le_refl _) plan.goal


def replace_goal {n : ℕ} (prob : PlanningTask n) (new_goal : VarSet n) : PlanningTask n :=
  PlanningTask.mk prob.varNames prob.actions' prob.init' new_goal
/-! ### PlanningTask.Path last-step extraction for regression -/

/-- Any non-empty path ending at a goal state contains an action that is regressable
    through the goal. Proved by induction: the last action in the path produces the
    goal state and must therefore be regressable. -/
lemma path_has_regressable_action {n : ℕ} (prob : PlanningTask n) (g : VarSet n)
    {s1 s2 : State n} (path : PlanningTask.Path (replace_goal prob g) s1 s2)
    (hgoal : (replace_goal prob g).GoalState s2)
    (hlen : 0 < path.length) :
    ∃ a ∈ prob.actions', regressable' a (state'_of_varset' g) = true := by
  induction path with
  | empty => exact absurd hlen (by unfold PlanningTask.Path.length; omega)
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
lemma plan_last_step_decomposition {n : ℕ} (prob : PlanningTask n) (g : VarSet n)
    {s : BitVec n} (plan : PlanningTask.Plan (replace_goal prob g) (convertState s))
    (hng : ¬ satisfies' g s = true) :
    ∃ (a : Action n) (s_prev : State n) (prefix_path : PlanningTask.Path (replace_goal prob g) (convertState s) s_prev),
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
      PlanningTask.Path.cons_to_snoc ha succ rest
    refine ⟨a_last, s_prev, prefix_path, mem_actions'_of_mem_actions ha_last,
            successor_goal_implies_regressable a_last s_prev last g succ_last goal,
            succ_last, ?_, ?_⟩
    · -- Cost decomposition
      show prefix_path.cost + a_last.cost = (PlanningTask.Path.cons a s_mid ha succ rest).cost
      rw [heq, PlanningTask.Path.cost_snoc]
    · -- GoalState of s_prev for regressed goal
      exact predecessor_satisfies_regressed_goal a_last s_prev last g succ_last goal

/-
If a is regressable through g, then applying a to a state satisfying regress(a,g)
    gives a state satisfying g. This allows constructing a plan for prob_g from
    a plan for prob_{regress(a,g)} by appending action a.
-/
lemma apply_regressable_achieves_goal {n : ℕ} (a : Action n)
    (s_prev : State n) (g : VarSet n)
    (hreg : regressable' a (state'_of_varset' g) = true)
    (hprev : convertVarSet (varset'_of_state' (regress' a (state'_of_varset' g))) ⊆ s_prev) :
    convertVarSet g ⊆ (s_prev \ a.del) ∪ a.add := by
  intro i hi; by_cases hi' : i ∈ a.del <;> simp_all +decide [ regressable' ] ;
  · cases hreg i hi' <;> tauto;
  · unfold convertVarSet varset'_of_state' regress' state'_of_varset' at hprev; simp_all [ Set.subset_def, VarSet.mem_iff ] ;
    grind

noncomputable def cast_path_replace_goal {n : ℕ} (prob : PlanningTask n) (g1 g2 : VarSet n)
    {s1 s2 : State n} (path : PlanningTask.Path (replace_goal prob g1) s1 s2) :
    PlanningTask.Path (replace_goal prob g2) s1 s2 := by
  induction path with
  | empty s => exact PlanningTask.Path.empty s
  | cons a s2 ha succ rest ih => exact PlanningTask.Path.cons a s2 ha succ ih

lemma cast_path_replace_goal_cost {n : ℕ} (prob : PlanningTask n) (g1 g2 : VarSet n)
    {s1 s2 : State n} (path : PlanningTask.Path (replace_goal prob g1) s1 s2) :
    (cast_path_replace_goal prob g1 g2 path).cost = path.cost := by
  induction path with
  | empty => rfl
  | cons a s2 ha succ rest ih =>
    unfold cast_path_replace_goal; simp only [PlanningTask.Path.cost]; exact congrArg (· + a.cost) ih

lemma cast_path_replace_goal_length {n : ℕ} (prob : PlanningTask n) (g1 g2 : VarSet n)
    {s1 s2 : State n} (path : PlanningTask.Path (replace_goal prob g1) s1 s2) :
    (cast_path_replace_goal prob g1 g2 path).length = path.length := by
  induction path with
  | empty => rfl
  | cons a s2 ha succ rest ih =>
    unfold cast_path_replace_goal; simp only [PlanningTask.Path.length]; exact congrArg (· + 1) ih

/-
For a regressable action, h(prob_g)(s) ≤ a.cost + h(prob_{regress(a,g)})(s).
    Requires h to be perfect (not just invariant-satisfying) because we need
    optimal plan existence to construct the extended plan.
    The previous version with `perfect_heuristic_invariant` was too weak:
    the forward invariant allows h < opt due to zero-cost cycles, breaking
    the argument.
-/
/-- Membership in the abstract set of a run-time state: `i ∈ convertVarSet (varset'_of_state' t)`
iff bit `i` of `t` is set. -/
lemma mem_convertVarSet_varset'_of_state' {n : ℕ} (t : BitVec n) (i : Fin n) :
    i ∈ convertVarSet (varset'_of_state' t) ↔ t[i.val] := by
  simp [convertVarSet, varset'_of_state', VarSet.mem_iff]

/-- The preconditions of an action are contained in the set regressed through any state. -/
lemma pre_subset_convert_regress {n : ℕ} (a : Action n) (s : BitVec n) :
    SetLike.coe a.pre ⊆ convertVarSet (varset'_of_state' (regress' a s)) := by
  intro i hi
  rw [mem_convertVarSet_varset'_of_state']
  have hpre : (a.pre.toBitVec)[i.val] = true := by
    rw [VarSet.getElem_toBitVec]
    simpa using Action.mem_pre.mp hi
  simp only [regress', BitVec.getElem_or, hpre, Bool.or_true]

lemma heur_le_regressable_action_cost {n : ℕ} (prob : PlanningTask n)
    (h : PlanningTask n → BitVec n → ℕ∞) (g : VarSet n) (s : BitVec n)
    (hperf : ∀ g' : VarSet n, heur_is_perfect (replace_goal prob g') (h (replace_goal prob g')))
    (a : Action n) (ha : a ∈ prob.actions')
    (hreg : regressable' a (state'_of_varset' g) = true) :
    h (replace_goal prob g) s ≤ a.cost + h (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' g)))) s := by
  set g' : VarSet n := varset'_of_state' (regress' a (state'_of_varset' g)) with hg'
  by_cases hsolv : Nonempty (PlanningTask.Plan (replace_goal prob g') (convertState s))
  · -- The regressed goal is solvable: extend an optimal plan for it by the action `a`.
    obtain ⟨plan', hplan'⟩ := (hperf g').2.1 s hsolv
    -- `a` is applicable at the end of `plan'` (its preconditions are part of the regressed goal).
    have happ : Applicable plan'.last a :=
      (pre_subset_convert_regress a (state'_of_varset' g)).trans plan'.goal
    have ha_act : a ∈ (replace_goal prob g).actions := by
      simp only [PlanningTask.actions, replace_goal, Finset.mem_coe, List.mem_toFinset]; exact ha
    -- successor of `plan'.last` under `a`.
    have hsucc : Successor a plan'.last ((plan'.last \ a.del) ∪ a.add) := ⟨happ, rfl⟩
    -- The extended path reaches a state satisfying the original goal `g`.
    refine le_trans ((hperf g).1 s
      ⟨(plan'.last \ a.del) ∪ a.add,
        PlanningTask.Path.snoc a plan'.last ha_act (cast_path_replace_goal prob g' g plan'.path) hsucc,
        apply_regressable_achieves_goal a plan'.last g hreg plan'.goal⟩) ?_
    -- Its cost equals `a.cost + h(regressed)`.
    have hcost : (PlanningTask.Path.snoc a plan'.last ha_act
        (cast_path_replace_goal prob g' g plan'.path) hsucc).cost
        = plan'.path.cost + a.cost := by
      rw [PlanningTask.Path.cost_snoc, cast_path_replace_goal_cost]
    simp only [hcost]
    push_cast
    rw [hplan', add_comm]
  · -- The regressed goal is unsolvable: its perfect value is `⊤`, so the bound is trivial.
    rw [not_nonempty_iff] at hsolv
    rw [(hperf g').2.2 s hsolv]
    exact le_top

lemma heur_eq_last_action_cost {n : ℕ} (prob : PlanningTask n)
    (h : PlanningTask n → BitVec n → ℕ∞) (g : VarSet n) (s : BitVec n)
    (hperf : ∀ g' : VarSet n, heur_is_perfect (replace_goal prob g') (h (replace_goal prob g')))
    (hs : Nonempty (PlanningTask.Plan (replace_goal prob g) (convertState s)))
    (hng : ¬ satisfies' g s = true) :
    ∃ a ∈ prob.actions'.filter (fun a => regressable' a (state'_of_varset' g)),
      a.cost + h (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' g)))) s =
        h (replace_goal prob g) s := by
          obtain ⟨ plan, hplan ⟩ := hperf g |>.2.1 s hs;
          obtain ⟨a, s_prev, prefix_path, ha, hreg, hsucc, hcost, hprev⟩ := plan_last_step_decomposition prob g plan (by
          exact hng);
          have hcost_eq : h (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' g)))) s ≤ prefix_path.cost := by
            have := hperf ( varset'_of_state' ( regress' a ( state'_of_varset' g ) ) ) |>.1 s ⟨ s_prev, cast_path_replace_goal prob g ( varset'_of_state' ( regress' a ( state'_of_varset' g ) ) ) prefix_path, hprev ⟩ ; simp_all 
            exact this.trans ( by rw [ cast_path_replace_goal_cost ] );
          have hcost_eq : a.cost + h (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' g))) ) s ≤ h (replace_goal prob g) s := by
            convert add_le_add_left hcost_eq ( a.cost : ℕ∞ ) using 1;
            · ring;
            · exact hplan.symm.trans ( mod_cast hcost.symm );
          have hcost_eq : h (replace_goal prob g) s ≤ a.cost + h (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' g))) ) s := by
            apply heur_le_regressable_action_cost prob h g s hperf a ha hreg;
          exact ⟨ a, List.mem_filter.mpr ⟨ ha, hreg ⟩, le_antisymm ‹_› ‹_› ⟩

def perfect_heuristic_regression_invariant {n : ℕ} (prob : PlanningTask n) (h : PlanningTask n → BitVec n → ℕ∞):=
  ∀ s : BitVec n, ∀ g : VarSet n,(
    Nonempty (PlanningTask.Plan (replace_goal prob g) (convertState s)) → (
      -- consider any potential goal
      if satisfies' g s then h (replace_goal prob g) s = 0
      else
      (
        let regressi : List (Action n) := prob.actions'.filter (fun a => regressable' a (state'_of_varset' g))
        regressi ≠ [] ∧ Option.some (h (replace_goal prob g) s) =
          (regressi.map (fun a => a.cost + h (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' g)))) s)).min?
    )
  )) ∧
    (IsEmpty (PlanningTask.Plan (replace_goal prob g) (convertState s)) → (h (replace_goal prob g) s) = ⊤)


/-- If h is perfect for all goals, then it satisfies the regression invariant.
    Note: the previous version used `perfect_heuristic_invariant` as hypothesis,
    which is strictly weaker and insufficient. -/
lemma perfect_regression_invar_of_is_perfect {n : ℕ} (prob : PlanningTask n)
    (h : PlanningTask n → BitVec n → ℕ∞) :
    (∀ g : VarSet n, heur_is_perfect (replace_goal prob g) (h (replace_goal prob g))) →
      perfect_heuristic_regression_invariant prob h := by
  intro hperf _s _hs
  have _hinv : ∀ g : VarSet n, perfect_heuristic_invariant (replace_goal prob g) (h (replace_goal prob g)) :=
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
          exact heur_le_regressable_action_cost prob h _hs _s hperf a ha_mem.1 ha_mem.2
  · intro isEmpty
    exact (hperf _hs).2.2 _s isEmpty

/-
From the regression invariant, extract the inequality h(g)(s) ≤ a.cost + h(regress(a,g))(s)
    for any regressable action a when s is solvable and doesn't satisfy g.
-/
lemma regression_invariant_le {n : ℕ} (prob : PlanningTask n)
    (h : PlanningTask n → BitVec n → ℕ∞)
    (hinv : perfect_heuristic_regression_invariant prob h)
    (g : VarSet n) (s : BitVec n)
    (hs : Nonempty (PlanningTask.Plan (replace_goal prob g) (convertState s)))
    (hng : ¬ satisfies' g s = true)
    (a : Action n) (ha : a ∈ prob.actions')
    (hreg : regressable' a (state'_of_varset' g) = true) :
    h (replace_goal prob g) s ≤ a.cost + h (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' g)))) s := by
  have := hinv s g;
  cases h : List.min? ( List.map ( fun a => ( a.cost : ℕ∞ ) + h ( replace_goal prob ( varset'_of_state' ( regress' a ( state'_of_varset' g ) ) ) ) s ) ( List.filter ( fun a => regressable' a ( state'_of_varset' g ) ) prob.actions' ) ) <;> simp_all +decide [ List.min?_eq_some_iff ];
  grind

lemma goal_aware_of_regression_invariant {n : ℕ} (prob : PlanningTask n)
    (h : PlanningTask n → BitVec n → ℕ∞)
    (hinv : perfect_heuristic_regression_invariant prob h)
    (g : VarSet n) (s : BitVec n)
    (hsat : satisfies' g s = true) :
    h (replace_goal prob g) s = 0 := by
      have := ( hinv s g );
      convert this.1 ?_;
      · grobner;
      · refine' ⟨ ⟨ _, _, _ ⟩ ⟩;
        exact convertState s;
        · exact PlanningTask.Path.empty _;
        · exact satisfies'_implies_GoalState (replace_goal prob g) s hsat

/-
Auxiliary lemma: plan cost ≥ h for the regression invariant, by induction on plan length.
    Quantified over ALL goals simultaneously so the IH applies to regressed goals.
-/
private lemma plan_cost_ge_heur_of_regression_aux {n : ℕ} (prob : PlanningTask n)
    (h : PlanningTask n → BitVec n → ℕ∞)
    (hinv : perfect_heuristic_regression_invariant prob h)
    (k : ℕ) (g : VarSet n) {start : BitVec n} {goal : State n}
    (path : PlanningTask.Path (replace_goal prob g) (convertState start) goal)
    (hlen : path.length ≤ k)
    (goal_state : (replace_goal prob g).GoalState goal) :
    path.cost ≥ h (replace_goal prob g) start := by
  induction' k with k ih generalizing g start goal;
  · cases path <;> simp_all +decide [ PlanningTask.Path.length ];
    exact goal_aware_of_regression_invariant prob h hinv g start ( GoalState_implies_satisfies' _ _ goal_state );
  · have := hinv start g;
    cases' em ( satisfies' g start ) with hsat hsat <;> simp_all +decide;
    · exact this.1 ⟨ goal, path, goal_state ⟩ ▸ zero_le;
    · rcases path with ( _ | ⟨ a, s_mid, ha, succ, rest ⟩ ) <;> simp_all +decide [ PlanningTask.Path.length ];
      · exact absurd ( GoalState_implies_satisfies' ( replace_goal prob g ) start goal_state ) ( by aesop );
      · obtain ⟨s_prev, a_last, ha_last, prefix_path, succ_last, heq, hlen'⟩ := PlanningTask.Path.cons_to_snoc ha succ rest;
        have hcost_eq : h (replace_goal prob g) start ≤ a_last.cost + h (replace_goal prob (varset'_of_state' (regress' a_last (state'_of_varset' g)))) start := by
          apply regression_invariant_le prob h hinv g start;
          · exact ⟨ ⟨ goal, PlanningTask.Path.cons a s_mid ha succ rest, goal_state ⟩ ⟩;
          · simp_all [ satisfies' ];
          · exact List.mem_dedup.mp ha_last;
          · exact successor_goal_implies_regressable a_last s_prev goal g succ_last goal_state;
        have hcost_eq : h (replace_goal prob (varset'_of_state' (regress' a_last (state'_of_varset' g)))) start ≤ prefix_path.cost := by
          convert ih _ ( cast_path_replace_goal prob g ( varset'_of_state' ( regress' a_last ( state'_of_varset' g ) ) ) prefix_path ) _ _ using 1;
          · exact_mod_cast cast_path_replace_goal_cost prob g ( varset'_of_state' ( regress' a_last ( state'_of_varset' g ) ) ) prefix_path |> Eq.symm;
          · rw [ cast_path_replace_goal_length ] ; linarith;
          · exact predecessor_satisfies_regressed_goal a_last s_prev goal g succ_last goal_state;
        rw [ heq, PlanningTask.Path.cost_snoc ];
        exact le_trans ‹_› ( by rw [ add_comm ] ; exact add_le_add_left hcost_eq _ )

lemma admissible_of_regression_invariant {n : ℕ} (prob : PlanningTask n)
    (h : PlanningTask n → BitVec n → ℕ∞) :
    perfect_heuristic_regression_invariant prob h →
    (∀ g : VarSet n, heur_admissible (replace_goal prob g) (h (replace_goal prob g))) := by
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
if an action `a` has `a.pre ⊆ g`, `a.add ∩ g = ∅`, `a.del ∩ g = ∅`, and `a.cost = 0`,
then `regress(a, g) = g`, creating a zero-cost self-loop in the regression Bellman equation.
This allows `h(g)(s)` to take any value ≤ opt in the regression invariant, while the
forward invariant may force a unique (larger) value.

The correct equivalence is:
`(∀ g, heur_is_perfect (replace_goal prob g) (h ...)) ↔ perfect_heuristic_regression_invariant prob h`
where `heur_is_perfect` additionally requires optimal plan existence.
-/




def weaker_than_perfect_heuristic_regression_invariant {n : ℕ} (prob : PlanningTask n) (h : PlanningTask n → BitVec n → ℕ∞):=
  ∀ s : BitVec n, ∀ g : VarSet n,(
    Nonempty (PlanningTask.Plan (replace_goal prob g) (convertState s)) → (
      -- consider any potential goal
      if satisfies' g s then h (replace_goal prob g) s = 0
      else
      (
        let regressi : List (Action n) := prob.actions'.filter (fun a => regressable' a (state'_of_varset' g))
        regressi ≠ [] ∧ Option.some (h (replace_goal prob g) s) ≤ -- actual heuristic value might be lower
          (regressi.map (fun a => a.cost + h (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' g)))) s)).min?
    )
  )) ∧
    (IsEmpty (PlanningTask.Plan (replace_goal prob g) (convertState s)) → (h (replace_goal prob g) s) = ⊤)

/-
From the weaker regression invariant, extract the key inequality: h(g,s) ≤ a.cost + h(regress(a,g), s).
-/
lemma weaker_regression_invariant_le {n : ℕ} (prob : PlanningTask n)
    (h : PlanningTask n → BitVec n → ℕ∞)
    (hinv : weaker_than_perfect_heuristic_regression_invariant prob h)
    (g : VarSet n) (s : BitVec n)
    (hs : Nonempty (PlanningTask.Plan (replace_goal prob g) (convertState s)))
    (hng : ¬ satisfies' g s = true)
    (a : Action n) (ha : a ∈ prob.actions')
    (hreg : regressable' a (state'_of_varset' g) = true) :
    h (replace_goal prob g) s ≤ a.cost + h (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' g)))) s := by
  have := hinv s g
  simp_all
  split_ifs at this
  · grind;
  · cases h : List.min? ( List.map ( fun a => ( a.cost : ℕ∞ ) + h ( replace_goal prob ( varset'_of_state' ( regress' a ( state'_of_varset' g ) ) ) ) s ) ( List.filter ( fun a => regressable' a ( state'_of_varset' g ) ) prob.actions' ) ) <;> simp_all [ List.min?_eq_some_iff ];
    exact this.2.trans ( h.2 _ _ ha hreg rfl )

lemma goal_aware_of_weaker_regression_invariant {n : ℕ} (prob : PlanningTask n)
    (h : PlanningTask n → BitVec n → ℕ∞)
    (hinv : weaker_than_perfect_heuristic_regression_invariant prob h)
    (g : VarSet n) (s : BitVec n)
    (hsat : satisfies' g s = true) :
    h (replace_goal prob g) s = 0 := by
  convert hinv s g |>.1 _ using 1
  · lia
  · refine' ⟨ ⟨ convertState s, PlanningTask.Path.empty _, _ ⟩ ⟩
    exact satisfies'_implies_GoalState (replace_goal prob g) s hsat

/-
Auxiliary: plan cost ≥ h for the weaker regression invariant, by induction on plan length.
-/
private lemma plan_cost_ge_heur_of_weaker_regression_aux {n : ℕ} (prob : PlanningTask n)
    (h : PlanningTask n → BitVec n → ℕ∞)
    (hinv : weaker_than_perfect_heuristic_regression_invariant prob h)
    (k : ℕ) (g : VarSet n) {start : BitVec n} {goal : State n}
    (path : PlanningTask.Path (replace_goal prob g) (convertState start) goal)
    (hlen : path.length ≤ k)
    (goal_state : (replace_goal prob g).GoalState goal) :
    path.cost ≥ h (replace_goal prob g) start := by
  induction' k with k ih generalizing g start goal;
  · cases path <;> simp_all +decide [ PlanningTask.Path.length ];
    exact goal_aware_of_weaker_regression_invariant prob h hinv g start ( GoalState_implies_satisfies' _ _ goal_state );
  · by_cases hsat : satisfies' g start;
    · rw [ goal_aware_of_weaker_regression_invariant prob h hinv g start hsat ] ; norm_num;
    · rcases path with ( _ | ⟨ a, s_mid, ha, succ, rest ⟩ ) <;> simp_all +decide [ PlanningTask.Path.length ];
      · exact absurd ( GoalState_implies_satisfies' ( replace_goal prob g ) start goal_state ) ( by aesop );
      · obtain ⟨s_prev, a_last, ha_last, prefix_path, succ_last, heq, hlen'⟩ := PlanningTask.Path.cons_to_snoc ha succ rest;
        have hcost_eq : h (replace_goal prob g) start ≤ a_last.cost + h (replace_goal prob (varset'_of_state' (regress' a_last (state'_of_varset' g)))) start := by
          apply weaker_regression_invariant_le prob h hinv g start ⟨⟨goal, PlanningTask.Path.cons a s_mid ha succ rest, goal_state⟩⟩ (by
          unfold satisfies'; aesop;) a_last (List.mem_dedup.mp ha_last) (successor_goal_implies_regressable a_last s_prev goal g succ_last goal_state);
        have hcost_eq : h (replace_goal prob (varset'_of_state' (regress' a_last (state'_of_varset' g)))) start ≤ prefix_path.cost := by
          convert ih _ ( cast_path_replace_goal prob g ( varset'_of_state' ( regress' a_last ( state'_of_varset' g ) ) ) prefix_path ) _ _ using 1;
          · exact_mod_cast cast_path_replace_goal_cost prob g ( varset'_of_state' ( regress' a_last ( state'_of_varset' g ) ) ) prefix_path |> Eq.symm;
          · rw [ cast_path_replace_goal_length ] ; linarith;
          · exact predecessor_satisfies_regressed_goal a_last s_prev goal g succ_last goal_state;
        rw [ heq, PlanningTask.Path.cost_snoc ];
        exact le_trans ‹_› ( by rw [ add_comm ] ; exact add_le_add_left hcost_eq _ )

lemma admissible_of_weaker_regression_invariant {n : ℕ} (prob : PlanningTask n)
    (h : PlanningTask n → BitVec n → ℕ∞) :
    weaker_than_perfect_heuristic_regression_invariant prob h →
    (∀ g : VarSet n, heur_admissible (replace_goal prob g) (h (replace_goal prob g))) := by
  intro hinv g v plan
  exact plan_cost_ge_heur_of_weaker_regression_aux prob h hinv plan.path.length g plan.path
    (le_refl _) plan.goal


def bellman_heuristic_regression_invariant {n : ℕ} (prob : PlanningTask n) (h : PlanningTask n → BitVec n → ℕ∞):=
∀ s : BitVec n, ∀ g : VarSet n,
-- consider any potential goal
if satisfies' g s then h (replace_goal prob g) s = 0
else
let regressi : List (Action n) := prob.actions'.filter (fun a => regressable' a (state'_of_varset' g))
if r : regressi = [] then
h (replace_goal prob g) s = ⊤
else
let minCostPredecessor := (regressi.map (fun a => a.cost + h (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' g)))) s)).min (by simp_all)

if minCostPredecessor = ⊤ then -- if unsolvable then still unsolvable
h (replace_goal prob g) s = ⊤
else
h (replace_goal prob g) s ≤ minCostPredecessor

/-
From the bellman regression invariant, extract the key inequality: h(g,s) ≤ a.cost + h(regress(a,g), s)
    when g is not satisfied and the min regression cost is below threshold.
-/
lemma bellman_regression_invariant_le {n : ℕ} (prob : PlanningTask n)
    (h : PlanningTask n → BitVec n → ℕ∞)
    (hinv : bellman_heuristic_regression_invariant prob h)
    (g : VarSet n) (s : BitVec n)
    (hng : ¬ satisfies' g s = true)
    (a : Action n) (ha : a ∈ prob.actions')
    (hreg : regressable' a (state'_of_varset' g) = true)
    (h_finite : h (replace_goal prob g) s ≠ ⊤) :
    h (replace_goal prob g) s ≤ a.cost + h (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' g)))) s := by
  specialize hinv s g;
  split_ifs at hinv
  simp_all 
  exact hinv.choose_spec.2.trans ( by exact List.min_le_of_mem ( List.mem_map.mpr ⟨ a, List.mem_filter.mpr ⟨ ha, hreg ⟩, rfl ⟩ ) )

lemma goal_aware_of_bellman_regression_invariant {n : ℕ} (prob : PlanningTask n)
    (h : PlanningTask n → BitVec n → ℕ∞)
    (hinv : bellman_heuristic_regression_invariant prob h)
    (g : VarSet n) (s : BitVec n)
    (hsat : satisfies' g s = true) :
    h (replace_goal prob g) s = 0 := by
  have := hinv s g
  simp_all only [↓reduceIte]

/-
Auxiliary: plan cost ≥ h for the bellman regression invariant, by induction on plan length.
-/
private lemma plan_cost_ge_heur_of_bellman_regression_aux {n : ℕ} (prob : PlanningTask n)
    (h : PlanningTask n → BitVec n → ℕ∞)
    (hinv : bellman_heuristic_regression_invariant prob h)
    (k : ℕ) (g : VarSet n) {start : BitVec n} {goal : State n}
    (path : PlanningTask.Path (replace_goal prob g) (convertState start) goal)
    (hlen : path.length ≤ k)
    (goal_state : (replace_goal prob g).GoalState goal) :
    path.cost ≥ h (replace_goal prob g) start := by
  induction' k with k ih generalizing g start goal;
  · cases path <;> simp_all +decide [ PlanningTask.Path.length ];
    exact goal_aware_of_bellman_regression_invariant prob h hinv g start ( GoalState_implies_satisfies' _ _ goal_state );
  · by_cases hsat : satisfies' g start;
    · exact goal_aware_of_bellman_regression_invariant prob h hinv g start hsat ▸ zero_le;
    · rcases path with ( _ | ⟨ a, s_mid, ha, succ, rest ⟩ ) <;> simp_all +decide [ PlanningTask.Path.length ];
      · exact absurd ( GoalState_implies_satisfies' _ _ goal_state ) ( by aesop );
      · obtain ⟨s_prev, a_last, ha_last, prefix_path, succ_last, heq, hlen'⟩ := PlanningTask.Path.cons_to_snoc ha succ rest
        have hreg := successor_goal_implies_regressable a_last s_prev goal g succ_last goal_state
        have ha_last' := List.mem_dedup.mp ha_last;
        have hcost_eq : h (replace_goal prob g) start ≤ a_last.cost + h (replace_goal prob (varset'_of_state' (regress' a_last (state'_of_varset' g)))) start := by
          apply bellman_regression_invariant_le;
          · assumption;
          · unfold satisfies'; aesop;
          · exact ha_last';
          · exact hreg;
          · have h_finite : h (replace_goal prob (varset'_of_state' (regress' a_last (state'_of_varset' g)))) start ≤ prefix_path.cost := by
              convert ih _ ( cast_path_replace_goal prob g ( varset'_of_state' ( regress' a_last ( state'_of_varset' g ) ) ) prefix_path ) _ _ using 1;
              · exact_mod_cast cast_path_replace_goal_cost prob g ( varset'_of_state' ( regress' a_last ( state'_of_varset' g ) ) ) prefix_path |> Eq.symm;
              · rw [ cast_path_replace_goal_length ] ; linarith;
              · exact predecessor_satisfies_regressed_goal a_last s_prev goal g succ_last goal_state;
            have := hinv start g; split_ifs at this ; simp_all 
            simp at *
            split_ifs at this <;> simp_all 
            · exact absurd ( ‹∀ a ∈ prob.actions', regressable' a ( state'_of_varset' g ) = false› a_last ha_last' ) ( by simp [ hreg ] )
            · rename_i h₁ h₂ h₃;
              contrapose! h₃;
              refine' ne_of_lt ( lt_of_le_of_lt ( List.min_le_of_mem _ ) _ );
              exact ↑a_last.cost + h ( replace_goal prob ( varset'_of_state' ( regress' a_last ( state'_of_varset' g ) ) ) ) start;
              · exact List.mem_map.mpr ⟨ a_last, List.mem_filter.mpr ⟨ ha_last', hreg ⟩, rfl ⟩;
              · exact ENat.add_lt_top.mpr ⟨ ENat.coe_lt_top _, lt_of_le_of_lt h_finite ( ENat.coe_lt_top _ ) ⟩;
            · exact ne_of_lt ( lt_of_le_of_lt this ( lt_top_iff_ne_top.mpr ‹_› ) );
        have hcost_eq : h (replace_goal prob (varset'_of_state' (regress' a_last (state'_of_varset' g)))) start ≤ prefix_path.cost := by
          convert ih _ ( cast_path_replace_goal prob g ( varset'_of_state' ( regress' a_last ( state'_of_varset' g ) ) ) prefix_path ) _ _ using 1;
          · exact_mod_cast cast_path_replace_goal_cost prob g ( varset'_of_state' ( regress' a_last ( state'_of_varset' g ) ) ) prefix_path |> Eq.symm;
          · rw [ cast_path_replace_goal_length ] ; linarith;
          · exact predecessor_satisfies_regressed_goal a_last s_prev goal g succ_last goal_state;
        rw [ heq, PlanningTask.Path.cost_snoc ];
        exact le_trans ‹_› ( by rw [ add_comm ] ; exact add_le_add_left hcost_eq _ )

lemma admissible_of_bellman_regression_invariant {n : ℕ} (prob : PlanningTask n)
    (h : PlanningTask n → BitVec n → ℕ∞) :
    bellman_heuristic_regression_invariant prob h →
    (∀ g : VarSet n, heur_admissible (replace_goal prob g) (h (replace_goal prob g))) := by
  intro hinv g s hs;
  exact plan_cost_ge_heur_of_bellman_regression_aux prob h hinv hs.path.length g hs.path ( by rfl ) hs.goal



def h_1_heuristic_regression_invariant {n : ℕ} (prob : PlanningTask n) (h : PlanningTask n → BitVec n → ℕ∞):=
  ∀ s : BitVec n, ∀ g : VarSet n,
      -- consider any potential goal
      if satisfies' g s then h (replace_goal prob g) s = 0
      else
        if g_at_least_two : g.toList.length > 1 then
          h (replace_goal prob g) s ≤ (g.toList.map (fun g' => h (replace_goal prob (singletonVarSet g')) s)).max (by intro h2; simp_all)
        else
          ∀ a ∈ prob.actions', regressable' a (state'_of_varset' g) = true →
            h (replace_goal prob g) s ≤ a.cost + h (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' g)))) s

/--
The h_1 regression invariant implies the pointwise bellman bound for single-atom goals.
-/
lemma h_1_implies_bellman_for_singletons {n : ℕ} (prob : PlanningTask n)
    (h : PlanningTask n → BitVec n → ℕ∞)
    (hinv : h_1_heuristic_regression_invariant prob h)
    (g : Fin n) (s : BitVec n)
    (hng : ¬ satisfies' (singletonVarSet g) s = true)
    (a : Action n) (ha : a ∈ prob.actions')
    (hreg : regressable' a (state'_of_varset' (singletonVarSet g)) = true) :
    h (replace_goal prob (singletonVarSet g)) s ≤
      a.cost + h (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' (singletonVarSet g))))) s := by
  have hlen : ¬ (singletonVarSet g).toList.length > 1 := by
    rw [← List.toFinset_card_of_nodup (VarSet.toList_nodup _)]
    have heq : (singletonVarSet g).toList.toFinset = {g} := by
      ext x
      simp [singletonVarSet, VarSet.ofList]
    rw [heq]
    simp
  have hi := hinv s (singletonVarSet g)
  simp only [hng, hlen] at hi
  exact hi a ha hreg

lemma plan_for_conjunction_gives_plan_for_atom {n : ℕ} (prob : PlanningTask n)
    (g : VarSet n) (g' : Fin n) (hg' : g' ∈ g.toList)
    (s : BitVec n) (plan : PlanningTask.Plan (replace_goal prob g) (convertState s)) :
    Nonempty (PlanningTask.Plan (replace_goal prob (singletonVarSet g')) (convertState s)) := by
  refine' ⟨ ⟨ _, _, _ ⟩ ⟩;
  exact plan.last;
  · exact cast_path_replace_goal prob g (singletonVarSet g') plan.path;
  · have := plan.goal; simp_all [ replace_goal, PlanningTask.GoalState ] ;
    exact fun x hx => this <| by
      have hx' : x = g' := by simpa [singletonVarSet, VarSet.ofList] using hx
      subst x
      exact hg' ;

/-- Goal-awareness from the h_1 regression invariant: if the state satisfies the goal, h = 0. -/
lemma goal_aware_of_h_1_regression_invariant {n : ℕ} (prob : PlanningTask n)
    (h : PlanningTask n → BitVec n → ℕ∞)
    (hinv : h_1_heuristic_regression_invariant prob h)
    (g : VarSet n) (s : BitVec n)
    (hsat : satisfies' g s = true) :
    h (replace_goal prob g) s = 0 := by
  have := hinv s g; simp [hsat] at this; exact this

/-- For any goal g with the h_1 regression invariant, h(g,s) ≤ max of singleton values when |g| > 1. -/
lemma h_1_multi_atom_le_singletons {n : ℕ} (prob : PlanningTask n)
    (h : PlanningTask n → BitVec n → ℕ∞)
    (hinv : h_1_heuristic_regression_invariant prob h)
    (g : VarSet n) (s : BitVec n)
    (hng : ¬ satisfies' g s = true)
    (hlen : g.toList.length > 1) :
    h (replace_goal prob g) s ≤ (g.toList.map (fun g' => h (replace_goal prob (singletonVarSet g')) s)).max (by intro h2; simp_all) := by
  have := hinv s g; simp [hng] at this; simp [hlen] at this; exact this

/-
Given bounds on singleton goals, derive bounds on any goal.
    If every singleton goal [g'] has h([g'],s) ≤ C, then h(g,s) ≤ C for any g.
-/
lemma h_1_any_goal_le_of_singleton_bound {n : ℕ} (prob : PlanningTask n)
    (h : PlanningTask n → BitVec n → ℕ∞)
    (hinv : h_1_heuristic_regression_invariant prob h)
    (g : VarSet n) (start : BitVec n) (C : ℕ)
    (hsat_or_bound :
      satisfies' g start = true ∨
      (∀ g' ∈ g.toList, h (replace_goal prob (singletonVarSet g')) start ≤ C)) :
    h (replace_goal prob g) start ≤ C := by
  by_cases hsat : satisfies' g start;
  · have := goal_aware_of_h_1_regression_invariant prob h hinv g start hsat; aesop;
  · by_cases hlen : g.toList.length > 1;
    · have := h_1_multi_atom_le_singletons prob h hinv g start hsat hlen;
      refine' le_trans this _;
      rw [ List.max_le_iff ];
      simp +zetaDelta at *;
      exact hsat_or_bound.resolve_left fun h => by obtain ⟨ x, hx₁, hx₂ ⟩ := hsat; specialize h x hx₁; aesop;
    · rcases k : g.toList with ( _ | ⟨ g', _ | ⟨ g'', l ⟩ ⟩ ) <;> simp_all +decide [ satisfies' ];
      · replace k := congr_arg List.toFinset k; simp_all +decide [ Finset.ext_iff ] ;
      · have h_singleton : g = singletonVarSet g' := by
          apply SetLike.ext
          intro x
          constructor
          · intro hx
            have hm := congrArg (fun l => x ∈ l) k
            have heq : x = g' := by simpa using (hm.mp (by simpa using hx))
            subst x
            simp [singletonVarSet, VarSet.ofList]
          · intro hx
            have heq : x = g' := by simpa [singletonVarSet, VarSet.ofList] using hx
            subst x
            have hm := congrArg (fun l => g' ∈ l) k
            exact (by simpa using hm.symm)
        grind

private lemma h_1_invariant_singleton_bellman {n : ℕ} (prob : PlanningTask n)
    (h : PlanningTask n → BitVec n → ℕ∞)
    (hinv : h_1_heuristic_regression_invariant prob h)
    (g_atom : Fin n) (s : BitVec n)
    (hng : ¬ satisfies' (singletonVarSet g_atom) s = true)
    (a : Action n) (ha : a ∈ prob.actions')
    (hreg : regressable' a (state'_of_varset' (singletonVarSet g_atom)) = true) :
    h (replace_goal prob (singletonVarSet g_atom)) s ≤
      a.cost + h (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' (singletonVarSet g_atom))))) s := by
  -- Apply the hypothesis `hinv` with the given conditions.
  apply h_1_implies_bellman_for_singletons prob h hinv g_atom s hng a ha hreg

private lemma goalState_atom_of_goalState_conjunction {n : ℕ} (prob : PlanningTask n)
    (rg : VarSet n) (g' : Fin n) (hg' : g' ∈ rg.toList)
    {s_prev : State n}
    (hgoal : (replace_goal prob rg).GoalState s_prev) :
    (replace_goal prob (singletonVarSet g')).GoalState s_prev := by
  -- Since $g'$ is in $rg$, and $rg$ is the goal, $s_prev$ must satisfy $g'$.
  have h_g'_in_rg : convertVarSet (singletonVarSet g') ⊆ convertVarSet rg := by
    -- Since $g'$ is in $rg$, the singleton set $\{g'\}$ is a subset of $rg$.
    intro x hx
    have hx' : x = g' := by simpa [convertVarSet, singletonVarSet, VarSet.ofList] using hx
    subst x
    simpa using hg'
  exact Set.Subset.trans h_g'_in_rg hgoal

private lemma h_1_singleton_plan_cost_ge_heur_aux {n : ℕ} (prob : PlanningTask n)
    (h : PlanningTask n → BitVec n → ℕ∞)
    (hinv : h_1_heuristic_regression_invariant prob h)
    (k : ℕ) (g_atom : Fin n) {start : BitVec n} {goal : State n}
    (path : PlanningTask.Path (replace_goal prob (singletonVarSet g_atom)) (convertState start) goal)
    (hlen : path.length ≤ k)
    (goal_state : (replace_goal prob (singletonVarSet g_atom)).GoalState goal) :
    path.cost ≥ h (replace_goal prob (singletonVarSet g_atom)) start := by
  induction' k with k ih generalizing g_atom start goal
  · cases path <;> simp_all +decide [ PlanningTask.Path.length ]
    exact goal_aware_of_h_1_regression_invariant prob h hinv (singletonVarSet g_atom) start
      (GoalState_implies_satisfies' _ _ goal_state)
  · by_cases hsat : satisfies' (singletonVarSet g_atom) start
    · exact goal_aware_of_h_1_regression_invariant prob h hinv (singletonVarSet g_atom) start hsat ▸ zero_le
    · rcases path with _ | ⟨ a, s_mid, ha, succ, rest ⟩
      · exact absurd (GoalState_implies_satisfies' _ _ goal_state) hsat
      · obtain ⟨s_prev, a_last, ha_last, prefix_path, succ_last, heq, hlen'⟩ := PlanningTask.Path.cons_to_snoc ha succ rest
        have hreg := successor_goal_implies_regressable a_last s_prev goal (singletonVarSet g_atom) succ_last goal_state
        have ha_last' := List.mem_dedup.mp ha_last
        have hprefix_len : prefix_path.length ≤ k := by
          have hc : (PlanningTask.Path.cons a s_mid ha succ rest).length ≤ k + 1 := hlen
          simp only [PlanningTask.Path.length] at hc
          omega
        set rg := varset'_of_state' (regress' a_last (state'_of_varset' (singletonVarSet g_atom))) with hrg
        have hgoal_rg : (replace_goal prob rg).GoalState s_prev :=
          predecessor_satisfies_regressed_goal a_last s_prev goal (singletonVarSet g_atom) succ_last goal_state
        have hbound : h (replace_goal prob rg) start ≤ prefix_path.cost := by
          apply h_1_any_goal_le_of_singleton_bound prob h hinv rg start prefix_path.cost
          right
          intro g'' hg''
          have gs'' := goalState_atom_of_goalState_conjunction prob rg g'' hg'' hgoal_rg
          have hcost := cast_path_replace_goal_cost prob (singletonVarSet g_atom) (singletonVarSet g'') prefix_path
          have hlen'' := cast_path_replace_goal_length prob (singletonVarSet g_atom) (singletonVarSet g'') prefix_path
          have hih := ih g'' (cast_path_replace_goal prob (singletonVarSet g_atom) (singletonVarSet g'') prefix_path)
            (by rw [hlen'']; omega) gs''
          rw [hcost] at hih
          exact hih
        have hle := h_1_invariant_singleton_bellman prob h hinv g_atom start hsat a_last ha_last' hreg
        rw [heq, PlanningTask.Path.cost_snoc]
        calc h (replace_goal prob (singletonVarSet g_atom)) start
            ≤ a_last.cost + h (replace_goal prob rg) start := hle
          _ ≤ a_last.cost + prefix_path.cost := by gcongr
          _ = ((prefix_path.cost + a_last.cost : ℕ) : ℕ∞) := by push_cast; ring

private lemma h_1_any_goal_plan_cost_ge_heur {n : ℕ} (prob : PlanningTask n)
    (h : PlanningTask n → BitVec n → ℕ∞)
    (hinv : h_1_heuristic_regression_invariant prob h)
    (g : VarSet n) {start : BitVec n} {goal : State n}
    (path : PlanningTask.Path (replace_goal prob g) (convertState start) goal)
    (goal_state : (replace_goal prob g).GoalState goal) :
    path.cost ≥ h (replace_goal prob g) start := by
  apply h_1_any_goal_le_of_singleton_bound prob h hinv g start path.cost
  right
  intro g' hg'
  have gs' := goalState_atom_of_goalState_conjunction prob g g' hg' goal_state
  have hcost := cast_path_replace_goal_cost prob g (singletonVarSet g') path
  have hih := h_1_singleton_plan_cost_ge_heur_aux prob h hinv
    (cast_path_replace_goal prob g (singletonVarSet g') path).length g'
    (cast_path_replace_goal prob g (singletonVarSet g') path) (le_refl _) gs'
  rw [hcost] at hih
  exact hih
lemma admissible_of_h_1_regression_invariant {n : ℕ} (prob : PlanningTask n)
    (h : PlanningTask n → BitVec n → ℕ∞) :
    h_1_heuristic_regression_invariant prob h →
    (∀ g : VarSet n, heur_admissible (replace_goal prob g) (h (replace_goal prob g))) := by
  intro hinv g v plan
  exact h_1_any_goal_plan_cost_ge_heur prob h hinv g plan.path plan.goal


end STRIPS
