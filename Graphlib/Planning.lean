import Validator.PlanningTask.Core
import Validator.PlanningTask.Basic
import Graphlib.NatGraph
import Graphlib.AStar

import Mathlib.Logic.Lemmas

namespace Validator

instance {n : ℕ} : FinEnum (BitVec n) :=
  FinEnum.ofList (List.range (2^n)) (by
    intro x
    simp
    use BitVec.toNat x
    grind)


def satisfies' {n : ℕ} (cond : VarSet' n) (state : State' n) : Bool :=
  cond.val.all (fun x => state[x])

def applicable' {n : ℕ} (a : Action n) (state : State' n) : Bool :=
  satisfies' a.pre' state

def is_successor' {n : ℕ} (a : Action n) (f t : State' n) : Bool :=
  (List.finRange n).all (fun x =>
    if a.add'.val.contains x then
      t[x]
    else if a.del'.val.contains x then
      ¬ t[x]
    else
      t[x] = f[x]
  )

def successor' {n : ℕ} (a : Action n) (f : State' n) : State' n :=
  BitVec.cast (by simp) (BitVec.ofBoolListLE ((List.finRange n).map (fun x =>
    if a.add'.val.contains x then
      True
    else if a.del'.val.contains x then
      False
    else
      f[x])))


theorem BitVec.getElem_ofBoolListLE {i : Nat} {bs : List Bool} (h : i < bs.length) :
  (BitVec.ofBoolListLE bs)[i] = bs[i] := by
  rw [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofBoolListLE]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by omega)]
  simp


lemma successor'_is_successor' {n : ℕ} (a : Action n) (f : State' n) :
    is_successor' a f (successor' a f) := by
  unfold is_successor' successor'
  simp
  intro x
  split_ifs <;> try (simp_all [BitVec.getElem_ofBoolListLE])




abbrev is_successor_state {n : ℕ} (prob : STRIPS n) (f t : State' n) :=
    prob.actions'.any (fun a => applicable' a f ∧ is_successor' a f t)


def cost_of {n : ℕ} (prob : STRIPS n) (f t : State' n) (is_succ : is_successor_state prob f t): ℕ :=
    let applicableActs := prob.actions'.filter (fun a => applicable' a f ∧ is_successor' a f t)
    let costs : List ℕ := applicableActs.map (fun x => x.cost)
    costs.min (by unfold costs applicableActs ; simp_all)


lemma min_fold_find {α β : Type u}  [LinearOrder β] (l : List α) (x : β) (f : α → β) (h : x ≠ List.foldl min (x) (List.map f l)):
  ∃ a ∈ l, f a = List.foldl min x (List.map f l) := by
  cases l
  · contradiction
  case cons head tail =>
    by_cases head_eq_min : f head = List.foldl min x (List.map f (head :: tail))
    · use head
      constructor
      · simp only [List.mem_cons, true_or]
      · exact head_eq_min
    ·
      unfold List.map List.foldl at ⊢ head_eq_min
      simp only [List.mem_cons, exists_eq_or_imp]
      right
      apply min_fold_find
      by_contra
      rw [←this] at head_eq_min
      have x_lt_head : x = x ⊓ f head := by
        expose_names
        rw [inst.min_def]
        grind
      grind

lemma min_map {α β : Type u} [LinearOrder β] (l : List α) (f : α → β) (h : l.map f ≠ []):
    ∃ a ∈ l, f a = (l.map f).min h := by
    cases l
    · grind
    · expose_names
      unfold List.min
      simp
      rw [or_iff_not_imp_left]; intro head_ne_min
      apply min_fold_find
      apply head_ne_min


def min_cost_action {n : ℕ} (prob : STRIPS n) (f t : State' n) (is_succ : is_successor_state prob f t): Action n :=
    let applicableActs := prob.actions'.filter (fun a => applicable' a f ∧ is_successor' a f t)
    -- TODO ideally use List.minOn in newer mathlib version
    let costs : List ℕ := applicableActs.map (fun x => x.cost)
    let minCost := costs.min (by unfold costs applicableActs ; simp_all)
    let opt_act := applicableActs.find? (·.cost = minCost)
    have is_act : opt_act.isSome = true := by
      unfold opt_act minCost costs
      simp
      apply min_map

    opt_act.get is_act

lemma min_cost_action_in_prob {n : ℕ} (prob : STRIPS n) (f t : State' n) (is_succ : is_successor_state prob f t):
    min_cost_action prob f t is_succ ∈ prob.actions' := by
    unfold min_cost_action
    simp
    apply List.get_find?_mem


def trans_of_STRIPS {n : ℕ} (prob : STRIPS n) : NatGraph (State' n) :=
  let edges : State' n → State' n → Prop := fun f t => is_successor_state prob f t

  let dg : Digraph (State' n) := Digraph.mk edges
  let dg_dec : DecidableRel dg.Adj := by infer_instance
  let cost : (u v : State' n) → dg.Adj u v → ℕ := fun f t adj =>
    cost_of prob f t (by unfold is_successor_state ; grind)

  WeightedDiGraph.mk dg cost dg_dec

def trans_of_STRIPS_goals {n : ℕ} (prob : STRIPS n) : List (State' n) := 
  (List.finRange (2^n)).filter (fun s => satisfies' prob.goal' s)

lemma is_successor_state_of_trans_STRIPS_adj {n : ℕ} (prob : STRIPS n) (s s' : State' n) (adj : (trans_of_STRIPS prob).Adj s s') :
    is_successor_state prob s s' := by
  unfold is_successor_state
  unfold trans_of_STRIPS at adj
  simp_all

lemma min_cost_action_creates_successor {n : ℕ} (prob : STRIPS n) (s s' : State' n) (adj : (trans_of_STRIPS prob).Adj s s') :
  Successor (min_cost_action prob s s' (is_successor_state_of_trans_STRIPS_adj prob s s' adj)) (convertState s) (convertState s') := by
  unfold Successor
  set a := min_cost_action prob s s' (is_successor_state_of_trans_STRIPS_adj prob s s' adj)
  constructor
  · unfold Applicable
    intro x x_in_find
    unfold convertState
    unfold Action.pre convertVarSet at x_in_find
    simp_all
    have appli_a : applicable' a s := by
      unfold a
      unfold min_cost_action
      grind
    unfold applicable' satisfies' at appli_a
    apply List.all_eq_true.mp at appli_a
    exact appli_a x x_in_find
  · unfold convertState
    simp
    apply Set.ext
    intro x
    simp
    have is_succ_a : is_successor' a s s' := by
      unfold a
      unfold min_cost_action
      grind
    unfold is_successor' at is_succ_a
    simp at is_succ_a
    specialize is_succ_a x
    split at is_succ_a
    · expose_names
      unfold Action.add
      unfold convertVarSet
      simp
      tauto
    · split at is_succ_a
      · expose_names
        simp_all
        unfold Action.add Action.del
        unfold convertVarSet
        simp
        tauto
      · rw [is_succ_a]
        unfold Action.add Action.del
        unfold convertVarSet
        simp
        tauto

def walk_to_strips_path {n : ℕ} (prob : STRIPS n) {start goal : State' n} (walk : WeightedDiGraph.Walk (G:= trans_of_STRIPS prob) start goal) (is_goal : satisfies' prob.goal' goal):
    Path prob (convertState start) (convertState goal):=
  match eq : walk with
  | .nil => Path.empty (convertState start)
  | .cons adj walk' => by
    expose_names
    have is_succ : is_successor_state prob start w := by
      apply is_successor_state_of_trans_STRIPS_adj
      exact adj
    let a : Action n := min_cost_action prob start w is_succ
    apply Path.cons (a := a) (s2 := convertState w)
    · unfold a
      unfold STRIPS.actions
      simp
      apply min_cost_action_in_prob
    · apply min_cost_action_creates_successor
      exact adj
    · apply walk_to_strips_path
      · exact walk'
      · exact is_goal

lemma convertState_injective {n} : Function.Injective (@convertState n) := by
  intro a b h
  ext i
  unfold convertState at h
  simp_all
  apply Set.ext_iff.mp at h
  expose_names
  specialize h ⟨i,hi⟩
  grind


lemma state_has_bitvec {n : ℕ} (s : State n) [DecidablePred s.Mem] : ∃ s' : State' n, convertState s' = s := by
  unfold State at s
  unfold convertState
  let l := (List.finRange n).map (fun x => decide (s.Mem x))
  have l_length : l.length = n := by grind
  let s' := BitVec.ofBoolListLE l
  use s'.cast l_length
  unfold s' l
  apply Set.ext
  intro x
  constructor
  · intro x_in
    simp_all
    rw [BitVec.getElem_ofBoolListLE] at x_in
    simp_all
    exact x_in
  · intro x_in
    simp_all
    rw [BitVec.getElem_ofBoolListLE]
    simp_all
    exact x_in


lemma adj_of_successor {n : ℕ} {a : Action n} (prob : STRIPS n) {s s' : State' n} (succ : Successor a (convertState s) (convertState s')) (ha : a ∈ prob.actions):
  (trans_of_STRIPS prob).Adj s s' := by
  unfold Successor convertState Applicable Action.pre Action.add Action.del convertVarSet at succ
  unfold trans_of_STRIPS
  simp_all
  use a
  constructor
  · unfold STRIPS.actions at ha
    simp at ha
    exact ha
  · constructor
    · unfold applicable' satisfies'
      simp
      intro x x_in_pre
      grind
    · unfold is_successor'
      simp
      intro x
      obtain ⟨_,eff⟩ := succ
      apply Set.ext_iff.mp at eff
      specialize eff x
      grind


noncomputable def successor_dec {n : ℕ} (a : Action n) (s s' : State n) (succ : Successor a s s'):
  DecidablePred (Set.Mem s') := by
  unfold DecidablePred
  intro i
  obtain ⟨ _, foo ⟩ := succ
  rw [foo]
  by_cases i_in_add : i ∈ a.add
  · apply isTrue
    apply Set.mem_union_right
    exact i_in_add
  · have union := (Set.mem_union (x:=i) (a:=s \ a.del) (b:=a.add)).mp
    by_cases i_in_del : i ∈ a.del
    · apply isFalse
      by_contra
      specialize union this
      grind
    · by_cases i_in_s : i ∈ s
      · apply isTrue
        apply Set.mem_union_left
        apply Set.mem_diff_of_mem
        · exact i_in_s
        · exact i_in_del
      · apply isFalse
        by_contra
        specialize union this
        cases union
        · expose_names
          apply (Set.mem_diff (x:=i)).mp at h
          simp_all
        · contradiction

noncomputable def strips_path_to_walk {n : ℕ} (prob : STRIPS n) {start goal : State' n} (path : Path prob (convertState start) (convertState goal)):
    WeightedDiGraph.Walk (G:= trans_of_STRIPS prob) start goal
  := by
    generalize hs : convertState start = s at path
    generalize hg : convertState goal = g at path
    cases path with
    | empty s =>
        have : start = goal := convertState_injective (hs.trans hg.symm)
        subst this
        exact WeightedDiGraph.Walk.nil
    | cons a s2 ha succ path' =>
      have s2_mem_dec : DecidablePred (Set.Mem s2) := successor_dec a s s2 succ
      have xx := state_has_bitvec s2
      let s2' := Classical.choose xx
      let s2'_eq_s2 := Classical.choose_spec xx
      apply WeightedDiGraph.Walk.cons (w:= s2')
      · apply adj_of_successor
        · rw [← hs] at succ
          rw [← s2'_eq_s2] at succ
          apply succ
        · exact ha
      · rw [← s2'_eq_s2] at path'
        rw [← hg] at path'
        apply strips_path_to_walk (path := path')
termination_by path.length
decreasing_by
  simp
  expose_names
  have f : path'.length < path.length := by
    have e := HEq.eq h_2
    rw [e]
    conv =>
      right
      unfold Validator.Path.length
    simp
  grind

noncomputable def last_dec {n : ℕ} (prob : STRIPS n) (s : State' n) (last : State n) (path : Path prob (convertState s) last) :
    DecidablePred (Set.Mem last) := by
  cases path
  · intro x
    unfold convertState
    by_cases s_i : s[x] = true
    · apply isTrue
      unfold Set.Mem
      exact s_i
    · apply isFalse
      exact s_i
  case cons a s2 ha succ path' =>
    have s2_mem_dec : DecidablePred (Set.Mem s2) := successor_dec a (convertState s) s2 succ
    have xx := state_has_bitvec s2
    let s2' := Classical.choose xx
    let s2'_eq_s2 := Classical.choose_spec xx
    apply last_dec (path:=s2'_eq_s2 ▸ path')
termination_by path.length
decreasing_by
  expose_names
  have f : π.length < path.length := by
    have e := HEq.eq h_2
    rw [e]
    conv =>
      right
      unfold Validator.Path.length
    simp
  grind


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

namespace Path

/-- The length of a path. -/
def cost {n} {pt : STRIPS n} {s s'} : Path pt s s' → ℕ
| Path.empty _ => 0
| Path.cons a _ _ _ π => π.cost + a.cost

end Path

/-! ### Helper lemmas for planner optimality -/

/-
PROBLEM
`min_cost_action` achieves the minimum cost, i.e., its cost equals `cost_of`.

PROVIDED SOLUTION
Unfold both `min_cost_action` and `cost_of`. They share the same `applicableActs` and `costs` definitions. `min_cost_action` finds an action via `find?` whose cost equals `costs.min`, and `cost_of` returns `costs.min`. So `min_cost_action.cost = costs.min = cost_of`. The key is that `find?` returns an element satisfying `·.cost = minCost` and `.get` extracts it, so `.cost = minCost`.
-/
lemma min_cost_action_cost_eq_cost_of {n : ℕ} (prob : STRIPS n) (f t : State' n)
    (is_succ : is_successor_state prob f t) :
    (min_cost_action prob f t is_succ).cost = cost_of prob f t is_succ := by
  unfold cost_of min_cost_action at *;
  grind only [List.get_find?_prop]

/-
PROBLEM
The edge cost in `trans_of_STRIPS` equals `cost_of`.

PROVIDED SOLUTION
Unfold `NatGraph.edgeCost` to get `G.Payload f t adj`. Unfold `trans_of_STRIPS` - the Payload is defined as `cost_of prob f t (some_proof)`. By `WeightedDiGraph.Payload_irr`, the proof doesn't matter, so this equals `cost_of prob f t (is_successor_state_of_trans_STRIPS_adj prob f t adj)`.
-/
lemma trans_of_STRIPS_edgeCost {n : ℕ} (prob : STRIPS n) (f t : State' n)
    (adj : (trans_of_STRIPS prob).Adj f t) :
    NatGraph.edgeCost adj = cost_of prob f t (is_successor_state_of_trans_STRIPS_adj prob f t adj) := by
  convert rfl

/-
PROBLEM
`cost_of` is at most the cost of any specific applicable action producing the transition.

PROVIDED SOLUTION
Unfold `cost_of`. The result is `costs.min h` where `costs = applicableActs.map (·.cost)` and `applicableActs = prob.actions'.filter (fun a => applicable' a f ∧ is_successor' a f t)`. Since `a ∈ prob.actions'` and `applicable' a f = true` and `is_successor' a f t = true`, we have `a ∈ applicableActs`. Therefore `a.cost ∈ costs`. And `List.min` is ≤ every element in the list. Use `List.min_le_of_mem` or similar.
-/
lemma cost_of_le_action_cost {n : ℕ} (prob : STRIPS n) (f t : State' n) (a : Action n)
    (is_succ : is_successor_state prob f t)
    (a_in_prob : a ∈ prob.actions')
    (a_applicable : applicable' a f = true) (a_produces : is_successor' a f t = true) :
    cost_of prob f t is_succ ≤ a.cost := by
  have h_a_in_applicableActs : a ∈ prob.actions'.filter (fun a => applicable' a f ∧ is_successor' a f t) := by
    grind +ring;
  apply List.min_le_of_mem;
  exact List.mem_map.mpr ⟨ a, h_a_in_applicableActs, rfl ⟩

/-
PROBLEM
The STRIPS path cost of `walk_to_strips_path` equals the graph walk cost.

PROVIDED SOLUTION
By induction on walk.
- nil case: both costs are 0 (Path.empty has cost 0, Walk.nil has cost 0).
- cons case: walk = cons adj walk'. walk_to_strips_path produces Path.cons (min_cost_action ...) ... (walk_to_strips_path walk'). STRIPS cost = (walk_to_strips_path walk').cost + (min_cost_action ...).cost. By IH, (walk_to_strips_path walk').cost = walk'.cost. And (min_cost_action ...).cost = cost_of ... = edgeCost adj (by min_cost_action_cost_eq_cost_of and trans_of_STRIPS_edgeCost). Walk.cost of cons = edgeCost adj + walk'.cost. So STRIPS cost = walk'.cost + edgeCost adj = edgeCost adj + walk'.cost = walk.cost.
-/
lemma walk_to_strips_path_cost_eq {n : ℕ} (prob : STRIPS n) {start goal : State' n}
    (walk : WeightedDiGraph.Walk (G := trans_of_STRIPS prob) start goal)
    (is_goal : satisfies' prob.goal' goal) :
    (walk_to_strips_path prob walk is_goal).cost = walk.cost := by
  revert walk is_goal;
  intro walk;
  induction walk;
  · intro is_goal
    simp_all only [WeightedDiGraph.Walk.cost_nil_zero]
    rfl
  · intro is_goal
    unfold walk_to_strips_path
    unfold Path.cost WeightedDiGraph.Walk.cost
    rw [ add_comm, min_cost_action_cost_eq_cost_of, trans_of_STRIPS_edgeCost ]
    simp_all

/-
PROBLEM
For any STRIPS plan, there exists a graph walk whose cost is at most the plan's path cost.

If action `a` is in `prob.actions` (Finset), then it's in `prob.actions'` (List).

PROVIDED SOLUTION
Use strips_path_to_walk to get a graph walk, then show its cost ≤ path.cost by induction on the path. Alternatively, construct the walk directly by induction on path:
- empty: use Walk.nil, cost 0 ≤ 0
- cons with action a, successor from s1 to s2, and rest path from s2 to goal:
  - s2 has a BitVec representation s2' (via state_has_bitvec, using successor_dec for decidability)
  - There's a graph edge from start to s2' (by adj_of_successor)
  - edgeCost = cost_of ≤ a.cost (by cost_of_le_action_cost, since a is applicable and produces the transition, and a ∈ prob.actions')
  - By IH on the rest path (from convertState s2' to convertState goal), get walk' with cost ≤ rest.cost
  - Combine: Walk.cons adj walk' with cost = edgeCost + walk'.cost ≤ a.cost + rest.cost = path.cost

Key: need to handle the DecidablePred for s2, use state_has_bitvec and Classical.choose. The function adj_of_successor gives the graph adjacency. cost_of_le_action_cost bounds the edge cost.

Need to handle termination carefully - use path.length as the termination measure, similar to strips_path_to_walk.

STRIPS.actions is defined as List.toFinset prob.actions'. So a ∈ prob.actions means a ∈ prob.actions'.toFinset, which implies a ∈ prob.actions'. Unfold STRIPS.actions and use List.mem_toFinset.
-/
lemma mem_actions'_of_mem_actions {n : ℕ} {prob : STRIPS n} {a : Action n}
    (ha : a ∈ prob.actions) : a ∈ prob.actions' := by
  exact List.mem_dedup.mp ha

/-
PROBLEM
If `Successor a (convertState s) (convertState t)` with `a ∈ prob.actions`,
    then `applicable' a s` and `is_successor' a s t`.

PROVIDED SOLUTION
Successor a (convertState s) (convertState t) gives us Applicable (convertState s) a, i.e., a.pre ⊆ convertState s. Unfold applicable' and satisfies'. We need a.pre'.val.all (fun x => s[x]) = true. By List.all_eq_true, this means for all x ∈ a.pre'.val, s[x] = true. Since a.pre ⊆ convertState s and a.pre = convertVarSet a.pre' = a.pre'.val.toFinset, for any x ∈ a.pre'.val, x ∈ a.pre'.val.toFinset = a.pre ⊆ convertState s = {i | s[i]}, so s[x] = true. This is the same logic as in the first part of adj_of_successor (unfold applicable' satisfies', then use the Applicable hypothesis via List.all_eq_true and simp/grind).
-/
lemma successor_implies_applicable {n : ℕ}
    {a : Action n} {s t : State' n}
    (succ : Successor a (convertState s) (convertState t)) :
    applicable' a s = true := by
  unfold applicable' satisfies' at *
  simp
  intro x hx
  have h_pre : x ∈ a.pre := by
    convert Finset.mem_coe.mpr ( Finset.mem_coe.mpr ( List.mem_toFinset.mpr hx ) ) using 1
  have h_s : s[x] := by
    exact Set.mem_setOf.mp ( succ.1 h_pre ) |> fun h => by simpa using h;
  exact h_s

lemma successor_implies_is_successor {n : ℕ}
    {a : Action n} {s t : State' n}
    (succ : Successor a (convertState s) (convertState t)) :
    is_successor' a s t = true := by
  unfold Successor convertState Applicable Action.pre Action.add Action.del convertVarSet at succ
  unfold is_successor'
  simp
  intro x
  obtain ⟨_,eff⟩ := succ
  apply Set.ext_iff.mp at eff
  specialize eff x
  simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_union, Finset.mem_coe, List.mem_toFinset] at eff
  split_ifs with h1 h2 <;> simp_all


private lemma strips_path_has_cheaper_walk_aux {n : ℕ} (prob : STRIPS n) (k : ℕ)
    {start goal : State' n}
    (path : Path prob (convertState start) (convertState goal))
    (hlen : path.length ≤ k) :
    ∃ w : WeightedDiGraph.Walk (G := trans_of_STRIPS prob) start goal, w.cost ≤ path.cost := by
  induction k generalizing start goal with
  | zero =>
    generalize hs : convertState start = s at path
    generalize hg : convertState goal = g at path
    cases path with
    | empty =>
      have : start = goal := convertState_injective (hs.trans hg.symm)
      subst this
      exact ⟨WeightedDiGraph.Walk.nil, le_refl 0⟩
    | cons => simp [Path.length] at hlen
  | succ k ih =>
    generalize hs : convertState start = s at path
    generalize hg : convertState goal = g at path
    cases path with
    | empty =>
      have : start = goal := convertState_injective (hs.trans hg.symm)
      subst this
      exact ⟨WeightedDiGraph.Walk.nil, le_refl 0⟩
    | cons a s2 ha succ path' =>
      subst hs; subst hg
      haveI := successor_dec a (convertState start) s2 succ
      obtain ⟨s2', rfl⟩ := state_has_bitvec s2
      have adj := adj_of_successor prob succ ha
      have path'_len : path'.length ≤ k := by
        simp [Path.length] at hlen; omega
      obtain ⟨walk', hw'⟩ := ih path' path'_len
      refine ⟨WeightedDiGraph.Walk.cons adj walk', ?_⟩
      have edge_le : NatGraph.edgeCost adj ≤ a.cost := by
        rw [trans_of_STRIPS_edgeCost]
        exact cost_of_le_action_cost prob start s2' a _
          (mem_actions'_of_mem_actions ha)
          (successor_implies_applicable succ)
          (successor_implies_is_successor succ)
      simp only [WeightedDiGraph.Walk.cost, Path.cost]
      omega

lemma strips_path_has_cheaper_walk {n : ℕ} (prob : STRIPS n) {start goal : State' n}
    (path : Path prob (convertState start) (convertState goal)) :
    ∃ w : WeightedDiGraph.Walk (G := trans_of_STRIPS prob) start goal, w.cost ≤ path.cost :=
  strips_path_has_cheaper_walk_aux prob path.length path (le_refl _)


abbrev heur_admissible {n : ℕ} (prob : STRIPS n) (heur : State' n → ℕ):=
  ∀ v : State' n, ∀ plan : Plan prob (convertState v), plan.path.cost ≥ (heur v)


abbrev heur_admissible' {n : ℕ} (prob : STRIPS n) (heur : State' n → ℕ):=
  ∀ v : State' n, ∀ goal ∈ trans_of_STRIPS_goals prob, ∀ path : WeightedDiGraph.Path (G:=trans_of_STRIPS prob) v goal, path.cost ≥ (heur v)



private lemma satisfies'_implies_GoalState {n : ℕ} (prob : STRIPS n) (goal : State' n)
    (h : satisfies' prob.goal' goal = true) :
    prob.GoalState (convertState goal) := by
  unfold STRIPS.GoalState convertVarSet convertState satisfies' at *
  simp_all [List.all_eq_true, Set.subset_def]

private lemma GoalState_implies_satisfies' {n : ℕ} (prob : STRIPS n) (goal : State' n)
    (h : prob.GoalState (convertState goal)) :
    satisfies' prob.goal' goal = true := by
  unfold STRIPS.GoalState convertVarSet convertState satisfies' at *
  simp_all [List.all_eq_true, Set.subset_def]

private lemma mem_trans_of_STRIPS_goals_iff {n : ℕ} (prob : STRIPS n) (goal : State' n) :
    goal ∈ trans_of_STRIPS_goals prob ↔ satisfies' prob.goal' goal = true := by
  unfold trans_of_STRIPS_goals
  simp
  exact fun _ => ⟨goal.toFin, rfl⟩

private lemma Path.cost_eq_of_cast {n : ℕ} {pt : STRIPS n} {s s1 s2 : State n}
    (h : s1 = s2) (p : Path pt s s2) :
    (show Path pt s s1 from h ▸ p).cost = p.cost := by
  subst h; rfl
lemma admissible_of_admissible' {n : ℕ} (prob : STRIPS n) (heur : State' n → ℕ):
    heur_admissible' prob heur → heur_admissible prob heur := by
  intro h' v plan
  -- Get a BitVec representation of plan.last
  haveI : DecidablePred (Set.Mem plan.last) := last_dec prob v plan.last plan.path
  obtain ⟨g', hg'⟩ := state_has_bitvec plan.last
  -- Convert STRIPS path to graph walk
  obtain ⟨w, hw⟩ := strips_path_has_cheaper_walk prob (hg' ▸ plan.path)
  -- Get a graph Path from the walk
  obtain ⟨p, hp⟩ := WeightedDiGraph.Walk.cheaper_path_exists w
  -- Show g' is in the goals list
  have g'_in_goals : g' ∈ trans_of_STRIPS_goals prob := by
    rw [mem_trans_of_STRIPS_goals_iff]
    exact GoalState_implies_satisfies' prob g' (hg' ▸ plan.goal)
  -- Apply admissible'
  have hge := h' v g' g'_in_goals p
  -- Cost preservation under cast
  have hcost : (hg' ▸ plan.path).cost = plan.path.cost :=
    Path.cost_eq_of_cast hg' plan.path
  omega

lemma admissible'_of_admissible {n : ℕ} (prob : STRIPS n) (heur : State' n → ℕ):
    heur_admissible prob heur → heur_admissible' prob heur := by
  intro h v goal goal_in_goals graphPath
  -- goal satisfies the goal condition
  have sat : satisfies' prob.goal' goal = true :=
    (mem_trans_of_STRIPS_goals_iff prob goal).mp goal_in_goals
  -- Convert graph path to STRIPS path
  let stripsPath := walk_to_strips_path prob graphPath.val sat
  -- Build a Plan
  have goal_sat := satisfies'_implies_GoalState prob goal sat
  let plan : Plan prob (convertState v) :=
    Plan.mk (convertState goal) stripsPath goal_sat
  -- Apply admissible
  have hplan := h v plan
  -- The costs are equal
  have cost_eq : plan.path.cost = graphPath.cost := by
    show stripsPath.cost = graphPath.cost
    rw [walk_to_strips_path_cost_eq, WeightedDiGraph.Path.cost_same]
  omega


lemma zero_heur_admissible' {n : ℕ} (prob : STRIPS n) : heur_admissible' prob (fun _ => 0) := by
  exact fun v goal h => fun p => Nat.zero_le _

lemma zero_heur_admissible {n : ℕ} (prob : STRIPS n) : heur_admissible prob (fun _ => 0) := by
  apply admissible_of_admissible' prob
  apply zero_heur_admissible'



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
        · have := plan.goal; unfold STRIPS.GoalState at this; unfold convertState at hg'
          unfold convertVarSet at this; unfold satisfies'; simp_all +decide [ Set.subset_def ] ;
          exact fun x hx => hg'.symm.subset ( this x hx );
  grind 



lemma planner_optimal {n : ℕ} (prob : STRIPS n) (heur : State' n → ℕ)
  (admissible : heur_admissible prob heur)
  (ret_plan : (planner prob heur).isSome):
  ∀ plan : Plan prob prob.init, plan.path.cost ≥ ((planner prob heur).get ret_plan).path.cost := by
  intro plan
  rw [planner_path_cost_eq_astar]
  exact plan_cost_ge_astar prob heur admissible (planner_isSome_implies_astar_isSome prob heur ret_plan) plan


lemma admissible_of_dominated_by_admissible {n : ℕ} (prob : STRIPS n) (h1 h2 : State' n → ℕ) (admissible : heur_admissible' prob h1) (dominated : ∀ s : State' n, h1 s ≥ h2 s) : heur_admissible' prob h2 := by sorry



def is_valid_abstraction {V V': Type} [FinEnum V] [FinEnum V'] (g : NatGraph V) (g' : NatGraph V') (abstraction : V → V') :=
  ∀ v : V, ∀ v' : V, g.Adj v v' → g'.Adj (abstraction v) (abstraction v')


def is_bisimulation {V V': Type} [FinEnum V] [FinEnum V'] (g : NatGraph V) (g' : NatGraph V') (abstraction : V → V') :=
  ∀ v : V, ∀ v' : V, g.Adj v v' ↔ g'.Adj (abstraction v) (abstraction v')



def max_action_cost {n : ℕ} (prob : STRIPS n) : ℕ := if empty : prob.actions'.length = 0 then 1 else 
  (prob.actions'.map (·.cost)).max (by rw [ne_eq] ; rw [List.map_eq_nil_iff] ; rw [←List.length_eq_zero_iff];  exact empty)

/-- A path cannot contain the same node twice. I.e. any path contains at most 2^n - 1 many actions and must thos be cheaper than 2^n times the maximum action cost. -/
lemma all_paths_shorter_than {n : ℕ} (prob : STRIPS n):
    ∀ goal ∈ trans_of_STRIPS_goals prob, ∀ path : WeightedDiGraph.Path (G:= (trans_of_STRIPS prob)) prob.init' goal, path.cost < (2^n) * (max_action_cost prob) := by sorry


def abstraction_heuristic {n : ℕ} (prob : STRIPS n) {V : Type} [FinEnum V] (g : NatGraph V) (abstraction: State' n → V) (s : State' n) : ℕ :=
  let goals := (trans_of_STRIPS_goals prob).map abstraction
  let opt_ret := NatGraph.astar_multigoal (g:=g) (fun _ => 0) (abstraction s) goals
  match opt_ret with
  | .none => (2^n) * (max_action_cost prob) 
  | .some ret =>
      ret.2.val.cost


lemma abstractions_admissible {n : ℕ} (prob : STRIPS n) {V : Type} [FinEnum V] {g : NatGraph V} (abstraction: State' n → V) (is_abstraction : is_valid_abstraction (trans_of_STRIPS prob) (g) abstraction) : 
  heur_admissible' prob (fun s => abstraction_heuristic prob g abstraction s)
    := by sorry

def delete_relax_action {n : ℕ} (a : Action n) : Action n := Action.mk a.name a.pre' a.add' ⟨[], by apply List.sortedLT_iff_pairwise.mpr ; simp ⟩  a.cost

def delete_relaxation {n : ℕ} (prob : STRIPS n) : STRIPS n := STRIPS.mk prob.varNames (prob.actions'.map delete_relax_action) prob.init' prob.goal'


def h_plus {n : ℕ} (prob : STRIPS n) (s : State' n) : ℕ :=
  let del_relax_ret := planner (delete_relaxation prob) (fun _ => 0)
  match del_relax_ret with
  | .none => (2^n) * (max_action_cost prob) 
  | .some ret => ret.path.cost

lemma h_plus_admissible {n : ℕ} (prob : STRIPS n) : heur_admissible' prob (h_plus prob) := by sorry

