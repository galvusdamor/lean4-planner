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


def planner {n : ℕ} (prob : STRIPS n) : Option (Plan prob prob.init) :=
  let trans := trans_of_STRIPS prob
  let ini := prob.init'
  let goals := (List.finRange (2^n)).filter (fun s => satisfies' prob.goal' s)
  let h : (State' n) → ℕ := fun _ => 0 

  let opt_ret := NatGraph.astar_multigoal (g:=trans) h ini goals 
  match opt_ret with
  | .none => .none
  | .some ret => 
    let goal' : State' n := ret.1
    have goal'_in_goals : goal' ∈ goals := by apply ret.1.prop

    have sat : satisfies' prob.goal' goal' := by
      unfold goals at goal'_in_goals
      simp at goal'_in_goals
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



lemma planner_complete {n : ℕ} (prob : STRIPS n):
      planner prob = Option.none → Unsolvable prob := by
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
    let zero_h : State' n → ℕ := fun _ => 0
    let goals : List (State' n) := (List.finRange (2^n)).filter (fun s => satisfies' prob.goal' s)

    have no_goal_path := mt (NatGraph.astar_multigoal_is_complete zero_h prob.init' goals) (by simp ; apply heq)
    push_neg at no_goal_path
    have goal'_in_goals : goal' ∈ goals := by
      unfold goals
      simp
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

--import Aesop
--
--import Mathlib.Data.Fintype.Basic
--import Mathlib.Data.Finset.Basic
--import Mathlib.Data.Finset.Lattice.Basic
--
--abbrev StripsState (nvar : Nat) := Finset (Fin nvar)
--
--structure StripsAction (nvar : Nat) where
--  pre : Finset (Fin nvar)
--  add : Finset (Fin nvar)
--  del : Finset (Fin nvar)
--  no_pre_added : pre ∩ add = ∅
--  no_del_added : add ∩ del = ∅
--
----
--
--def op : StripsAction 5 := StripsAction.mk {1} {2} {3} (by
--  apply Finset.inter_singleton_of_notMem
--  rw [← Finset.forall_mem_not_eq]
--  intro b b_in_1
--  rw [Finset.mem_singleton] at b_in_1
--  subst b_in_1 
--  rw [← Fin.val_inj]
--  exact Nat.succ_ne_self 1
--   ) (by
--  ext a
--  apply Iff.intro
--  · intro a_in
--    have f : False := by 
--      rw [Finset.mem_inter] at a_in
--      have ⟨ a2, a3 ⟩ := a_in
--      rw [Finset.mem_singleton] at a2
--      rw [Finset.mem_singleton] at a3
--      rw [a3] at a2
--      rw [← Fin.val_inj] at a2
--      exact Nat.succ_ne_self 2 a2
--    absurd f
--    simp only [not_false_eq_true]
--  · intro a_in_empty
--    absurd (Finset.notMem_empty a) a_in_empty 
--    simp only [not_false_eq_true]
--     ) 
--
--
--abbrev StripsActionSequence (nvar : Nat) (len : Nat) := Vector (StripsAction nvar) len
--
--structure StripsDomain (nvar : Nat) (nact : Nat) where
--  actions : Vector (StripsAction nvar) nact
--
--structure StripsProblem (nvar : Nat) (nact : Nat) where
--  domain : StripsDomain nvar nact
--  init : StripsState nvar
--  goal : StripsState nvar
--
--
--variable {nvar : Nat}
--variable {nact : Nat}
--
--
--def stripsApplicable (a: StripsAction nvar) (s : StripsState nvar) : Bool := a.pre ⊆ s
--
--def stripsApply (a: StripsAction nvar) (s : StripsState nvar) : (StripsState nvar) := (s \ a.del) ∪ a.add
--
--lemma two_applications_of_same_action_dont_change_state {a : StripsAction nvar} {s : StripsState nvar} :
--    stripsApply a s = stripsApply a (stripsApply a s) := by
--      unfold stripsApply
--      ext a_1
--      simp_all only [Finset.mem_union, Finset.mem_sdiff]
--      apply Iff.intro
--      · intro a_2
--        simp_all only [true_and]
--        cases a_2 with
--        | inl h => simp_all only [not_false_eq_true, true_or]
--        | inr h_1 => simp_all only [or_true]
--      · intro a_2
--        cases a_2 with
--        | inl h =>
--          simp_all only [not_false_eq_true, and_true]
--          obtain ⟨left, right⟩ := h
--          simp_all only [not_false_eq_true, and_true]
--        | inr h_1 => simp_all only [or_true]
--
--def stripsIsDeleteRelaxed (a: StripsAction nvar) := a.del = ∅
--
--lemma delete_relaxed_larger_state_is_better {a : StripsAction nvar} {s : StripsState nvar} {s' : StripsState nvar} : s ⊆ s' → (stripsApplicable a s) → stripsApplicable a s' := by
--  unfold stripsApplicable
--  simp
--  intro s_less_s' a_appli
--  apply Finset.Subset.trans
--  exact a_appli
--  exact s_less_s'
--
--
--
---- either returns none if not applicable or the state after the last action
--def stripsApplyActionSequence {l : Nat} (as : StripsActionSequence nvar l) (s : StripsState nvar) : Option (StripsState nvar) := 
--  if empty: l == 0 then (some s)
--  else 
--    let f : 0 < l := by
--      apply Nat.zero_lt_of_ne_zero
--      simp at empty
--      exact empty
--    let firstAction := as.get ⟨0, f⟩
--    let otherActions := as.tail
--    if !(stripsApplicable firstAction s) then none
--    else stripsApplyActionSequence otherActions (stripsApply firstAction s)
--
--
--def stripsActionSequenceApplicable {l : Nat} (as : StripsActionSequence nvar l) (s : StripsState nvar) : Bool := stripsApplyActionSequence as s != none 
--
--def stripsIsActionSequencePlan {l : Nat} (problem : StripsProblem nvar nact) (as : StripsActionSequence nvar l) : Bool :=
--  let result := stripsApplyActionSequence as problem.init
--  match result with
--   | none => False
--   | some s => problem.goal ⊆ s
--
--
--
--
--
--
--






