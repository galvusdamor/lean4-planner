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

def varset'_of_state' {n : ℕ} (s : State' n) : VarSet' n :=
  let l : List (Fin n) := (List.finRange n).filter (fun i => s[i])
  have l_s : l.SortedLT := by
    apply List.sortedLT_iff_pairwise.mpr
    unfold l
    apply List.Pairwise.filter
    apply List.pairwise_lt_finRange
  ⟨l, l_s⟩

def state'_of_varset' {n : ℕ} (v : VarSet' n) : State' n :=
  let l : List Bool := (List.finRange n).map (fun i => i ∈ v.1)
  have l_l : l.length = n := by unfold l; grind
  l_l ▸ BitVec.ofBoolListLE l


private lemma getElem_eq_rec_BitVec' {m n : ℕ} (h : m = n) (bv : BitVec m) (i : ℕ)
    (hi : i < n) :
    (show BitVec n from h ▸ bv)[i] = bv[i]'(by omega) := by
  subst h; rfl

theorem BitVec.getElem_ofBoolListLE {i : Nat} {bs : List Bool} (h : i < bs.length) :
  (BitVec.ofBoolListLE bs)[i] = bs[i] := by
  rw [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofBoolListLE]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem h]
  simp


/-- `state'_of_varset'` at index `i` checks membership in the var-set list. -/
lemma state'_of_varset'_getElem {n : ℕ} (v : VarSet' n) (i : Fin n) :
    (state'_of_varset' v)[i.val] = decide (i ∈ v.val) := by
  unfold state'_of_varset'
  rw [getElem_eq_rec_BitVec']
  rw [BitVec.getElem_ofBoolListLE]
  simp

/-- A variable is in `varset'_of_state'` iff it is true in the state. -/
lemma varset'_of_state'_mem {n : ℕ} (s : State' n) (i : Fin n) :
    i ∈ (varset'_of_state' s).val ↔ s[i.val] = true := by
  unfold varset'_of_state'
  simp [List.mem_filter]



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

-- an action can regress through a state if it does not delete anything that is true in the successor state
def regressable' {n : ℕ} (a : Action n) (s : State' n) : Bool :=
  a.del'.val.all (fun x => !s[x] ∨ (state'_of_varset' a.add')[x])

-- regress a through s. Note that this returns the minimally necessary state for the regression to be possible
def regress' {n : ℕ} (a : Action n) (s : State' n) : State' n :=
  BitVec.cast (by simp) (BitVec.ofBoolListLE ((List.finRange n).map (fun x =>
    if a.pre'.val.contains x then
      True
    else if a.add'.val.contains x then
      False -- after regression the state feature can be false
    else
      s[x])))


lemma successor'_is_successor' {n : ℕ} (a : Action n) (f : State' n) :
    is_successor' a f (successor' a f) := by
  unfold is_successor' successor'
  simp
  intro x
  split_ifs <;> try (simp_all [BitVec.getElem_ofBoolListLE])


lemma is_successor'_eq_successor' {n : ℕ} (a : Action n) (f t : State' n)
    (h : is_successor' a f t = true) : t = successor' a f := by
  unfold is_successor' at h
  unfold successor'
  ext i
  simp [BitVec.getElem_ofBoolListLE] at *
  specialize h ⟨i, by omega⟩
  split_ifs at h ⊢ <;> simp_all

lemma successor_regressable {n : ℕ} (a : Action n) (f : State' n):
    applicable' a f → regressable' a (successor' a f) := by
      unfold regressable';
      unfold successor';
      simp_all +decide [ BitVec.getElem_ofBoolListLE ];
      intro appli x x_in_del
      rw [state'_of_varset'_getElem]
      simp
      tauto
/-
f and (regress' a (successor' a f)) can differ in facts added and delete by a
-/
lemma successor_regress {n : ℕ} (a : Action n) (f : State' n) :
    applicable' a f → successor' a (regress' a (successor' a f)) = successor' a f := by
      intro ha
      ext x;
      erw [ BitVec.getElem_ofBoolListLE ];
      rw [ List.getElem_map, List.getElem_finRange ];
      erw [ BitVec.getElem_ofBoolListLE ] ; simp +decide [ List.getElem_finRange ] ;
      all_goals simp_all +decide [ successor' ];
      erw [ BitVec.getElem_ofBoolListLE ] ; simp +decide [ List.getElem_finRange ] ;
      unfold applicable' at ha; simp_all +decide [ satisfies' ] ;
      grind

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



namespace Path

/-- The length of a path. -/
def cost {n} {pt : STRIPS n} {s s'} : Path pt s s' → ℕ
| Path.empty _ => 0
| Path.cons a _ _ _ π => π.cost + a.cost

/-
The cost of a snoc path equals the prefix cost plus the appended action cost.
-/
lemma cost_snoc {n} {pt : STRIPS n} {a : Action n} {s1 s2 s3 : State n}
    {ha : a ∈ pt.actions} {path : Path pt s1 s2} {succ : Successor a s2 s3} :
    (Path.snoc a s2 ha path succ).cost = path.cost + a.cost := by
      unfold snoc;
      cases path <;> simp_all +arith +decide [ Path.cost ];
      rename_i a' s2' ha' succ' π';
      have h_ind : ∀ {s s' : State n} (a : Action n) (s1 s2 : State n) (ha : a ∈ pt.actions) (succ : Successor a s1 s2) (π : Path pt s s1), (snoc a s1 ha π succ).cost = π.cost + a.cost := by
        intros s s' a s1 s2 ha succ π;
        induction π;
        · exact?;
        · unfold snoc; simp_all +arith +decide [ Path.cost ] ;
      rw [ h_ind a s2 s3 ha succ π', add_comm ];
      exact s1
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
        simp [Path.length] at hlen; exact hlen
      obtain ⟨walk', hw'⟩ := ih path' path'_len
      refine ⟨WeightedDiGraph.Walk.cons adj walk', ?_⟩
      have edge_le : NatGraph.edgeCost adj ≤ a.cost := by
        rw [trans_of_STRIPS_edgeCost]
        exact cost_of_le_action_cost prob start s2' a _
          (mem_actions'_of_mem_actions ha)
          (successor_implies_applicable succ)
          (successor_implies_is_successor succ)
      show (WeightedDiGraph.Walk.cons adj walk').cost ≤
        (Path.cons a (convertState s2') ha succ path').cost
      simp only [WeightedDiGraph.Walk.cost, Path.cost]
      calc NatGraph.edgeCost adj + walk'.cost
          ≤ a.cost + path'.cost := Nat.add_le_add edge_le hw'
        _ = path'.cost + a.cost := Nat.add_comm _ _

lemma strips_path_has_cheaper_walk {n : ℕ} (prob : STRIPS n) {start goal : State' n}
    (path : Path prob (convertState start) (convertState goal)) :
    ∃ w : WeightedDiGraph.Walk (G := trans_of_STRIPS prob) start goal, w.cost ≤ path.cost :=
  strips_path_has_cheaper_walk_aux prob path.length path (le_refl _)



lemma satisfies'_implies_GoalState {n : ℕ} (prob : STRIPS n) (goal : State' n)
    (h : satisfies' prob.goal' goal = true) :
    prob.GoalState (convertState goal) := by
  unfold STRIPS.GoalState convertVarSet convertState satisfies' at *
  simp_all [List.all_eq_true, Set.subset_def]

lemma GoalState_implies_satisfies' {n : ℕ} (prob : STRIPS n) (goal : State' n)
    (h : prob.GoalState (convertState goal)) :
    satisfies' prob.goal' goal = true := by
  unfold STRIPS.GoalState convertVarSet convertState satisfies' at *
  simp_all [List.all_eq_true, Set.subset_def]

lemma mem_trans_of_STRIPS_goals_iff {n : ℕ} (prob : STRIPS n) (goal : State' n) :
    goal ∈ trans_of_STRIPS_goals prob ↔ satisfies' prob.goal' goal = true := by
  unfold trans_of_STRIPS_goals
  simp
  exact fun _ => ⟨goal.toFin, rfl⟩

lemma Path.cost_eq_of_cast {n : ℕ} {pt : STRIPS n} {s s1 s2 : State n}
    (h : s1 = s2) (p : Path pt s s2) :
    (show Path pt s s1 from h ▸ p).cost = p.cost := by
  subst h; rfl


def max_action_cost {n : ℕ} (prob : STRIPS n) : ℕ := if empty : prob.actions'.length = 0 then 1 else
  (prob.actions'.map (·.cost)).max (by rw [ne_eq] ; rw [List.map_eq_nil_iff] ; rw [←List.length_eq_zero_iff];  exact empty)


/-
PROVIDED SOLUTION
First, rewrite the edge cost using trans_of_STRIPS_edgeCost to get cost_of prob f t .... Then cost_of returns List.min of costs of applicable actions. This min ≤ any element in the list. The applicable actions are a subset of prob.actions'. Each action cost ≤ max_action_cost (which is List.max of all action costs, or 1 if empty). Use List.min_le_of_mem and List.le_max_of_mem, or just show cost_of ≤ some particular action's cost ≤ max_action_cost.

Rewrite edgeCost using trans_of_STRIPS_edgeCost. Then we have cost_of prob f t is_succ ≤ max_action_cost prob. Unfold cost_of and max_action_cost. The cost_of is List.min of applicable action costs. List.min is a member of the list (List.min_mem). Each applicable action is in prob.actions', so its cost is in the cost map of prob.actions'. By List.le_max_of_mem, each such cost ≤ List.max of all action costs. The max_action_cost uses if-then-else: if actions' empty then 1 else List.max. Since adj implies there's at least one applicable action, actions' is non-empty, so the if goes to else branch. Use split on the if, in the empty case derive contradiction from adj, in the non-empty case use List.min_le_of_mem and List.le_max_of_mem with transitivity.
-/
private lemma edge_cost_le_max_action_cost {n : ℕ} (prob : STRIPS n)
    {f t : State' n} (adj : (trans_of_STRIPS prob).Adj f t) :
    NatGraph.edgeCost adj ≤ max_action_cost prob := by
      -- Since cost_of returns the minimum cost of applicable actions and max_action_cost is the maximum cost of any action, we have cost_of prob f t ... ≤ max_action_cost prob.
      have h_cost_of_le_max : ∃ a ∈ prob.actions', a.cost = cost_of prob f t (is_successor_state_of_trans_STRIPS_adj prob f t adj) := by
        have h_cost_of_le_max : ∃ a ∈ prob.actions'.filter (fun a => applicable' a f ∧ is_successor' a f t), a.cost = cost_of prob f t (is_successor_state_of_trans_STRIPS_adj prob f t adj) := by
          unfold cost_of; simp only; exact min_map _ _ _
        generalize_proofs at *; (
        exact ⟨ h_cost_of_le_max.choose, List.mem_of_mem_filter h_cost_of_le_max.choose_spec.1, h_cost_of_le_max.choose_spec.2 ⟩)
      obtain ⟨a, ha_mem, ha_cost⟩ := h_cost_of_le_max
      have h_max_ge_a : a.cost ≤ max_action_cost prob := by
        unfold max_action_cost;
        split_ifs <;> simp_all +decide;
        exact List.le_max_of_mem ( List.mem_map.mpr ⟨ a, ha_mem, rfl ⟩ ) |> le_trans ha_cost.ge
      exact le_trans ha_cost.ge h_max_ge_a

/-
PROVIDED SOLUTION
By induction on w. Base case (nil): cost = 0 = 0 * bound. Cons case (cons adj rest): cost = edgeCost adj + rest.cost. By IH, rest.cost ≤ rest.length * bound. By h_edge, edgeCost adj ≤ bound. So cost ≤ bound + rest.length * bound = (1 + rest.length) * bound = w.length * bound.
-/
private lemma walk_cost_le_length_mul_bound {V : Type} [FinEnum V] {G : NatGraph V}
    {u v : V} (w : G.Walk u v) (bound : ℕ)
    (h_edge : ∀ (a b : V) (adj : G.Adj a b), NatGraph.edgeCost adj ≤ bound) :
    w.cost ≤ w.length * bound := by
      induction w;
      · simp +decide [ WeightedDiGraph.Walk.length ];
      · rw [ WeightedDiGraph.Walk.length, WeightedDiGraph.Walk.cost ];
        grind

/-
PROBLEM
A path cannot contain the same node twice. I.e. any path contains at most 2^n - 1 many
actions and its cost is at most 2^n times the maximum action cost.
Modified from the original statement: changed `<` to `≤` because the strict bound fails
when all action costs are zero.

PROVIDED SOLUTION
State' n = BitVec n. The FinEnum instance for BitVec n is defined via FinEnum.ofList (List.range (2^n)). Fintype.card for a FinEnum type equals FinEnum.card, which equals the length of FinEnum.toList. For ofList l proof, toList is defined as l.dedup or similar. The list used is List.range (2^n) which already has no duplicates (List.nodup_range). So the length is at most (List.range (2^n)).length = 2^n.
-/
private lemma fintype_card_state'_le (n : ℕ) : Fintype.card (State' n) ≤ 2^n := by
  have h : Fintype.card (State' n) = Fintype.card (Fin (2^n)) :=
    Fintype.card_congr {
      toFun := BitVec.toFin
      invFun := BitVec.ofFin
      left_inv := fun x => by simp
      right_inv := fun x => by simp
    }
  rw [h, Fintype.card_fin]

lemma all_paths_shorter_than {n : ℕ} (prob : STRIPS n):
    ∀ goal ∈ trans_of_STRIPS_goals prob, ∀ path : WeightedDiGraph.Path (G:= (trans_of_STRIPS prob)) prob.init' goal, path.cost ≤ (2^n) * (max_action_cost prob) := by
  intro goal _ path
  have h_cost := walk_cost_le_length_mul_bound path.val (max_action_cost prob)
    (fun a b adj => edge_cost_le_max_action_cost prob adj)
  have h_len_lt := path.path_length_lt_card
  calc path.cost = path.val.cost := WeightedDiGraph.Path.cost_same path
    _ ≤ path.val.length * max_action_cost prob := h_cost
    _ ≤ (Fintype.card (State' n) - 1) * max_action_cost prob :=
        Nat.mul_le_mul_right _ (Nat.le_sub_one_of_lt h_len_lt)
    _ ≤ Fintype.card (State' n) * max_action_cost prob :=
        Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    _ ≤ 2 ^ n * max_action_cost prob :=
        Nat.mul_le_mul_right _ (fintype_card_state'_le n)

/-
If an action produces a goal state from some predecessor, the action is regressable
    through the goal. This follows from the Successor definition: for each deleted variable
    that is in the goal, it must also be added (since it's in the successor despite deletion).
-/
lemma successor_goal_implies_regressable {n : ℕ} (a : Action n)
    (s goal : State n) (g : VarSet' n)
    (hsucc : Successor a s goal)
    (hgoal : convertVarSet g ⊆ goal) :
    regressable' a (state'_of_varset' g) = true := by
      simp_all [ regressable' ];
      intro x hx; specialize hgoal; simp [ convertVarSet, Set.subset_def ] at hgoal
      contrapose! hgoal; simp [ state'_of_varset'_getElem ] at hgoal
      use x;
      exact ⟨ hgoal.1, fun hx' => by
        have h_mem : ∀ (l : List (Fin n)), x ∈ l → x ∈ l.toFinset := by
          intro l a_1
          simp_all only [List.mem_toFinset]
        exact h_mem _ hx, fun hx' => hgoal.2 <| by
        exact List.mem_dedup.mp hx' ⟩

/-
If action a produces a goal state from s_prev, and a is regressable through g,
    then s_prev satisfies the regressed goal.
-/
lemma predecessor_satisfies_regressed_goal {n : ℕ} (a : Action n)
    (s_prev goal : State n) (g : VarSet' n)
    (hsucc : Successor a s_prev goal)
    (hgoal : convertVarSet g ⊆ goal) :
    convertVarSet (varset'_of_state' (regress' a (state'_of_varset' g))) ⊆ s_prev := by
      unfold Successor at hsucc; unfold convertVarSet;
      intro x hx; simp_all +decide [ Set.subset_def ] ;
      unfold varset'_of_state' at hx; unfold regress' at hx; simp_all [ List.finRange ] ;
      rw [ BitVec.getElem_ofBoolListLE ] at hx ; simp_all [ List.getElem_ofFn ] ;
      cases hx <;> simp_all [ convertVarSet ];
      · convert hsucc.1 x _;
        exact ( show x ∈ convertVarSet a.pre' from by simp [ convertVarSet, * ] );
      · cases hgoal x ( by
          rw [ state'_of_varset'_getElem ] at * ; aesop ) <;> simp_all [ state'_of_varset'_getElem ];
        rename_i h₁ h₂;
        cases h₁.1 (by
          exact List.mem_dedup.mp h₂
        )

/-- Any graph path in the STRIPS transition graph has cost ≤ 2^n * max_action_cost,
    regardless of its start and end states. -/
lemma graph_path_cost_le_bound {n : ℕ} (prob : STRIPS n) (s g : State' n)
    (path : WeightedDiGraph.Path (G := trans_of_STRIPS prob) s g) :
    path.cost ≤ 2 ^ n * max_action_cost prob := by
  have h_cost := walk_cost_le_length_mul_bound path.val (max_action_cost prob)
    (fun a b adj => edge_cost_le_max_action_cost prob adj)
  have h_len_lt := path.path_length_lt_card
  calc path.cost = path.val.cost := WeightedDiGraph.Path.cost_same path
    _ ≤ path.val.length * max_action_cost prob := h_cost
    _ ≤ (Fintype.card (State' n) - 1) * max_action_cost prob :=
        Nat.mul_le_mul_right _ (Nat.le_sub_one_of_lt h_len_lt)
    _ ≤ Fintype.card (State' n) * max_action_cost prob :=
        Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    _ ≤ 2 ^ n * max_action_cost prob :=
        Nat.mul_le_mul_right _ (fintype_card_state'_le n)
