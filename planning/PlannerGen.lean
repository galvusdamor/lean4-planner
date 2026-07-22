import SearchAlgorithms.MultigoalGen
import planning.Planner

/-!
# Generator-based STRIPS planner

This is a second implementation of the STRIPS planner built on the *generator-based* search of
`SearchAlgorithms` (`NatGraph.astar_multigoal_gen` from `SearchAlgorithms.MultigoalGen`).

Instead of exploring the transition system by testing the adjacency relation against *every*
state (as the enumeration-based `astar_multigoal` does), the generator-based search expands a
state by iterating over its explicit list of successors.  For STRIPS this successor list is
produced by iterating over the actions: the successors of a state `f` are the states
`successor' a f` for every action `a` applicable in `f`.

The underlying weighted digraph of the generator graph `trans_of_STRIPS_gen` is *definitionally*
the enumeration-based `trans_of_STRIPS`, so the generator-based planner computes exactly the
same result as `planner` (`planner_gen_eq`), and all its correctness properties transfer.
-/

namespace STRIPS

open NatGraph WeightedDiGraph

variable {n : ℕ}

/-- The action-based successor list of a state: for every applicable action, the resulting
successor state.  This is the list the generator iterates over instead of scanning all states. -/
def successorStates (prob : PlanningTask n) (f : BitVec n) : List (BitVec n) :=
  (prob.actions'.filter (fun a => applicable' a f)).map (fun a => successor' a f)

/-- Membership in `successorStates` is exactly the STRIPS adjacency relation. -/
lemma mem_successorStates (prob : PlanningTask n) (f t : BitVec n) :
    t ∈ successorStates prob f ↔ is_successor_state prob f t := by
  unfold successorStates is_successor_state
  simp only [List.mem_map, List.mem_filter, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨a, ⟨ha, happ⟩, rfl⟩
    exact ⟨a, ha, happ, successor'_is_successor' a f⟩
  · rintro ⟨a, ha, happ, hsucc⟩
    exact ⟨a, ⟨ha, happ⟩, (is_successor'_eq_successor' a f t hsucc).symm⟩

/-- The neighbour list used by the generator graph: the deduplicated, sorted (by numeric value)
action-successor list.  Sorting and deduplication are needed to satisfy the
`neighbours_sublist` invariant (the neighbour list must be an ordered sublist of the state
enumeration). -/
def transGenNeighbours (prob : PlanningTask n) (f : BitVec n) : List (BitVec n) :=
  ((successorStates prob f).dedup).mergeSort (fun a b => a.toNat ≤ b.toNat)

lemma mem_transGenNeighbours (prob : PlanningTask n) (f t : BitVec n) :
    t ∈ transGenNeighbours prob f ↔ is_successor_state prob f t := by
  unfold transGenNeighbours
  rw [List.Perm.mem_iff (List.mergeSort_perm _ _), List.mem_dedup, mem_successorStates]

/-
Reflection of `List.Sublist` under an injective map: if the images under an injective `f`
form a sublist, so do the originals.
-/
lemma sublist_of_map_sublist_of_injective {α β : Type*} {f : α → β} (hf : Function.Injective f)
    {l l' : List α} (h : (l.map f).Sublist (l'.map f)) : l.Sublist l' := by
  induction' l' with l' ih generalizing l;
  · aesop;
  · rcases l with ( _ | ⟨ x, l ⟩ ) <;> simp_all +decide [ List.sublist_cons_iff ];
    grind +splitIndPred

/-- `BitVec.toNat` is injective on `BitVec n = BitVec n`. -/
lemma toNat_injective_state : Function.Injective (BitVec.toNat : BitVec n → ℕ) :=
  BitVec.toNat_injective

/-- `FinEnum.toList` of an enumeration built from a duplicate-free exhaustive list returns that
list unchanged. -/
lemma toList_ofNodupList {α : Type*} [DecidableEq α] (xs : List α) (h : ∀ x, x ∈ xs)
    (h' : xs.Nodup) : @FinEnum.toList α (FinEnum.ofNodupList xs h h') = xs := by
  unfold FinEnum.toList FinEnum.ofNodupList
  simp only [FinEnum.card]
  exact List.map_get_finRange xs

/-- `FinEnum.toList` of an enumeration built from an exhaustive list returns that list
with duplicates removed. -/
lemma toList_ofList {α : Type*} [DecidableEq α] (xs : List α) (h : ∀ x, x ∈ xs) :
    @FinEnum.toList α (FinEnum.ofList xs h) = xs.dedup := by
  unfold FinEnum.ofList
  exact toList_ofNodupList _ _ _

set_option maxHeartbeats 1600000 in
/-- The enumeration of a decidable subtype `{x // p x}` is obtained by keeping the elements of
`FinEnum.toList α` that satisfy `p` (in the same order). -/
lemma toList_subtype {α : Type*} [FinEnum α] (p : α → Prop) [DecidablePred p] :
    @FinEnum.toList {x // p x} (FinEnum.Subtype.finEnum p) =
      ((FinEnum.toList α).filterMap fun x => if h : p x then some ⟨x, h⟩ else none) := by
  unfold FinEnum.Subtype.finEnum
  rw [toList_ofList, List.dedup_eq_self.2]
  apply List.Nodup.filterMap ?_ FinEnum.nodup_toList
  rintro a a' b h1 h2
  simp only [Option.mem_def] at h1 h2
  split at h1 <;> split at h2 <;> simp_all [Subtype.ext_iff]

/-- Enumerating the universal subtype and mapping back through the coercion recovers the
enumeration of the ambient type. -/
lemma toList_univ_subtype (α : Type*) [FinEnum α] :
    (FinEnum.toList ↥(Finset.univ : Finset α)).map Subtype.val = FinEnum.toList α := by
  rw [toList_subtype]
  simp only [Finset.mem_univ, dif_pos]
  rw [List.map_filterMap]
  simp [List.filterMap_some]

/-- Mapping the `BitVec n` enumeration through `BitVec.toNat` yields `List.range (2^n)`. -/
lemma toList_bitvec_toNat (n : ℕ) :
    (FinEnum.toList (BitVec n)).map BitVec.toNat = List.range (2 ^ n) := by
  show (@FinEnum.toList (BitVec n) instFinEnumBitVec).map _ = _
  rw [instFinEnumBitVec, toList_ofList]
  have hnd : (do let a ← List.range (2 ^ n); pure (↑a : BitVec n)).Nodup := by
    simp only [List.bind_eq_flatMap, List.pure_def, ← List.map_eq_flatMap]
    rw [List.nodup_map_iff_inj_on List.nodup_range]
    intro a ha b hb hab
    simp only [List.mem_range] at ha hb
    have : (a : BitVec n).toNat = (b : BitVec n).toNat := by rw [hab]
    rwa [BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
      BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb] at this
  rw [List.dedup_eq_self.2 hnd]
  simp only [List.bind_eq_flatMap, List.pure_def, ← List.map_eq_flatMap, List.map_map]
  rw [List.map_congr_left (g := id) ?_, List.map_id]
  intro a ha
  simp only [List.mem_range] at ha
  simp only [Function.comp, id, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]

/-
Mapping the state enumeration through `BitVec.toNat` yields `List.range (2^n)`; in
particular the enumeration is sorted by numeric value and has no duplicates.
-/
lemma enum_map_toNat :
    ((FinEnum.toList (Finset.univ : Finset (BitVec n)) : List (BitVec n))).map BitVec.toNat
      = List.range (2 ^ n) := by
  simp only [List.bind_eq_flatMap, List.pure_def, ← List.map_eq_flatMap, List.map_map]
  rw [show (BitVec.toNat ∘ fun a : ↥(Finset.univ : Finset (BitVec n)) => (↑a : BitVec n))
        = (BitVec.toNat ∘ Subtype.val) from rfl]
  rw [← List.map_map, toList_univ_subtype, toList_bitvec_toNat]
lemma transGenNeighbours_sublist (prob : PlanningTask n) (u : BitVec n) :
    (transGenNeighbours prob u).Sublist
      (FinEnum.toList (Finset.univ : Finset (BitVec n)) : List (BitVec n)) := by
  have h_sublist : List.Sublist (List.map BitVec.toNat (transGenNeighbours prob u)) (List.range (2^n)) := by
    apply List.sublist_of_subperm_of_sortedLE;
    · apply_rules [ List.Nodup.subperm ];
      · rw [ List.nodup_map_iff_inj_on ];
        · exact fun x hx y hy hxy => toNat_injective_state hxy;
        · exact List.Perm.nodup_iff ( List.mergeSort_perm _ _ ) |>.2 ( List.nodup_dedup _ );
      · intro x hx; obtain ⟨ y, hy, rfl ⟩ := List.mem_map.mp hx; exact List.mem_range.mpr ( BitVec.isLt _ ) ;
    · unfold transGenNeighbours;
      grind +suggestions;
    · exact fun i j hij => by simpa using hij;
  convert sublist_of_map_sublist_of_injective toNat_injective_state _ using 1;
  convert h_sublist using 1;
  convert enum_map_toNat

/-- STRIPS transition system as a `NatGraphWithGenerator`: the underlying weighted digraph is
`trans_of_STRIPS`, and the neighbour generator produces successors by iterating over the
actions. -/
def trans_of_STRIPS_gen (prob : PlanningTask n) : NatGraphWithGenerator (BitVec n) where
  toWeightedDiGraph := trans_of_STRIPS prob
  neighbours := transGenNeighbours prob
  neighbours_are_adj := by
    intro u v
    show is_successor_state prob u v ↔ v ∈ transGenNeighbours prob u
    rw [mem_transGenNeighbours]
  neighbours_sublist := transGenNeighbours_sublist prob

@[simp] lemma trans_of_STRIPS_gen_toWeightedDiGraph (prob : PlanningTask n) :
    (trans_of_STRIPS_gen prob).toWeightedDiGraph = trans_of_STRIPS prob := rfl

/-- The generator-based STRIPS planner: runs `astar_multigoal_gen` on the generator transition
system, then post-processes the resulting graph path into a STRIPS plan (exactly as `planner`
does for the enumeration-based search). -/
def planner_gen (prob : PlanningTask n) (heur : BitVec n → ℕ∞) : Option (PlanningTask.Plan prob prob.init) :=
  let ini := (state'_of_varset' prob.init')
  let goals := trans_of_STRIPS_goals prob

  let opt_ret := NatGraph.astar_multigoal_gen (trans_of_STRIPS_gen prob) heur ini
    (· ∈ goals)
  match opt_ret with
  | .none => .none
  | .some ret =>
    let goal' : BitVec n := ret.1
    have goal'_in_goals : goal' ∈ goals := ret.1.prop

    have sat : satisfies' prob.goal' goal' := by
      simp only [goals, trans_of_STRIPS_goals, List.mem_filter] at goal'_in_goals
      exact (satisfies'_iff prob.goal' goal').mpr ((satisfies'_iff prob.goal' goal').mp goal'_in_goals.2)

    let path : PlanningTask.Path prob (convertState ini) (convertState goal') := walk_to_strips_path prob ret.2.val sat
    have goal_sat : prob.GoalState (convertState goal') :=
      satisfies'_implies_GoalState prob goal' sat
    Option.some (PlanningTask.Plan.mk (convertState ret.fst) path goal_sat)

/-- The generator-based multi-goal A* on `trans_of_STRIPS_gen` computes the same result as the
enumeration-based list multi-goal A* on `trans_of_STRIPS`. -/
lemma astar_multigoal_gen_eq_list (prob : PlanningTask n) (heur : BitVec n → ℕ∞) :
    NatGraph.astar_multigoal_gen (trans_of_STRIPS_gen prob) heur (state'_of_varset' prob.init')
      (· ∈ trans_of_STRIPS_goals prob)
      = NatGraph.astar_multigoal (g := trans_of_STRIPS prob) heur (state'_of_varset' prob.init')
        (trans_of_STRIPS_goals prob) := by
  rw [NatGraph.astar_multigoal_gen_eq]
  rfl

/-- The generator-based planner returns exactly the same plan as the enumeration-based planner. -/
lemma planner_gen_eq (prob : PlanningTask n) (heur : BitVec n → ℕ∞) :
    planner_gen prob heur = planner prob heur := by
  simp only [planner_gen, planner, astar_multigoal_gen_eq_list]
  cases NatGraph.astar_multigoal (g := trans_of_STRIPS prob) heur (state'_of_varset' prob.init')
      (trans_of_STRIPS_goals prob) <;> rfl

/-- The direct goal *predicate* `satisfies' prob.goal'` equals membership in the enumerated goal
list `trans_of_STRIPS_goals`.  Using the predicate directly avoids ever materialising the list of
all `2^n` goal states, which is what makes the efficient planner fast. -/
lemma goal_pred_eq (prob : PlanningTask n) :
    (fun s : BitVec n => satisfies' prob.goal' s = true) = (· ∈ trans_of_STRIPS_goals prob) := by
  funext s
  rw [eq_iff_iff, mem_trans_of_STRIPS_goals_iff]

/-- Post-processing of a generator multi-goal A* result into a STRIPS plan, abstracted over the
goal predicate `is_goal` (together with a proof `hsub` that the predicate implies the STRIPS goal
is satisfied).  Both `planner_gen_fast` and `planner_gen` are this function applied to their
respective goal predicates. -/
def plan_of_gen_result (prob : PlanningTask n)
    (is_goal : BitVec n → Prop) [DecidablePred is_goal]
    (hsub : ∀ g : BitVec n, is_goal g → satisfies' prob.goal' g)
    (opt : Option ((thegoal : {v : BitVec n // is_goal v}) ×
      (trans_of_STRIPS_gen prob).toWeightedDiGraph.Path (state'_of_varset' prob.init') ↑thegoal)) :
    Option (PlanningTask.Plan prob prob.init) :=
  match opt with
  | none => none
  | some ret =>
    let goal' : BitVec n := ret.1
    have sat : satisfies' prob.goal' goal' := hsub ret.1 ret.1.prop
    let path : PlanningTask.Path prob (convertState (state'_of_varset' prob.init')) (convertState goal') :=
      walk_to_strips_path prob ret.2.val sat
    have goal_sat : prob.GoalState (convertState goal') :=
      satisfies'_implies_GoalState prob goal' sat
    some (PlanningTask.Plan.mk (convertState ret.fst) path goal_sat)

/-- The efficient generator-based STRIPS planner.  Identical to `planner_gen`, except the
multi-goal search is driven by the direct goal *predicate* `fun s => satisfies' prob.goal' s`
rather than by membership in the enumerated goal list `trans_of_STRIPS_goals prob`.  Because the
predicate is tested state-by-state, the search never enumerates the whole `2^n`-element state
space, so it runs in time proportional to the reachable part of the transition system. -/
def planner_gen_fast (prob : PlanningTask n) (heur : BitVec n → ℕ∞) : Option (PlanningTask.Plan prob prob.init) :=
  plan_of_gen_result prob (fun s => satisfies' prob.goal' s = true) (fun _ h => h)
    (NatGraph.astar_multigoal_gen (trans_of_STRIPS_gen prob) heur (state'_of_varset' prob.init')
      (fun s => satisfies' prob.goal' s = true))

/-- `plan_of_gen_result` depends on the goal predicate only up to equality: equal predicates and
`HEq` A* results give the same plan. -/
lemma plan_of_gen_result_congr (prob : PlanningTask n)
    (p q : BitVec n → Prop) [DecidablePred p] [DecidablePred q] (hpq : p = q)
    (hp : ∀ g : BitVec n, p g → satisfies' prob.goal' g)
    (hq : ∀ g : BitVec n, q g → satisfies' prob.goal' g)
    (op : Option ((thegoal : {v : BitVec n // p v}) ×
      (trans_of_STRIPS_gen prob).toWeightedDiGraph.Path (state'_of_varset' prob.init') ↑thegoal))
    (oq : Option ((thegoal : {v : BitVec n // q v}) ×
      (trans_of_STRIPS_gen prob).toWeightedDiGraph.Path (state'_of_varset' prob.init') ↑thegoal))
    (ho : HEq op oq) :
    plan_of_gen_result prob p hp op = plan_of_gen_result prob q hq oq := by
  subst hpq
  cases ho
  rfl

/-- The generator multi-goal A* result depends on the goal predicate only up to equality. -/
lemma astar_multigoal_gen_pred_heq {V : Type} [FinEnum V]
    (G : NatGraph.NatGraphWithGenerator V) (heur : V → ℕ∞) (start : V)
    (p q : V → Prop) [DecidablePred p] [DecidablePred q] (h : p = q) :
    HEq (NatGraph.astar_multigoal_gen G heur start p)
        (NatGraph.astar_multigoal_gen G heur start q) := by
  subst h
  congr 1
  exact Subsingleton.elim _ _

/-- The list-based generator planner is `plan_of_gen_result` applied to the goal-list membership
predicate. -/
lemma planner_gen_eq_plan_of_gen_result (prob : PlanningTask n) (heur : BitVec n → ℕ∞) :
    planner_gen prob heur
      = plan_of_gen_result prob (· ∈ trans_of_STRIPS_goals prob)
          (fun g h => (mem_trans_of_STRIPS_goals_iff prob g).mp h)
          (NatGraph.astar_multigoal_gen (trans_of_STRIPS_gen prob) heur (state'_of_varset' prob.init')
            (· ∈ trans_of_STRIPS_goals prob)) := by
  unfold planner_gen plan_of_gen_result
  dsimp only
  cases astar_multigoal_gen (trans_of_STRIPS_gen prob) heur (state'_of_varset' prob.init') (· ∈ trans_of_STRIPS_goals prob) <;>
    rfl

/-- The efficient predicate-based planner returns exactly the same plan as the list-based
generator planner (and hence as the enumeration-based `planner`). -/
lemma planner_gen_fast_eq (prob : PlanningTask n) (heur : BitVec n → ℕ∞) :
    planner_gen_fast prob heur = planner_gen prob heur := by
  rw [planner_gen_eq_plan_of_gen_result, planner_gen_fast]
  exact plan_of_gen_result_congr prob _ _ (goal_pred_eq prob) _ _ _ _
    (astar_multigoal_gen_pred_heq (trans_of_STRIPS_gen prob) heur (state'_of_varset' prob.init') _ _ (goal_pred_eq prob))

/-- Completeness of the generator-based planner (transferred from `planner_complete`). -/
lemma planner_gen_complete (prob : PlanningTask n) (heur : BitVec n → ℕ∞)
    (admissible : heur_admissible' prob heur) :
    planner_gen prob heur = Option.none → PlanningTask.Unsolvable prob := by
  rw [planner_gen_eq]
  exact planner_complete prob heur admissible

/-- Optimality of the generator-based planner (transferred from `planner_optimal`). -/
lemma planner_gen_optimal (prob : PlanningTask n) (heur : BitVec n → ℕ∞)
    (admissible : heur_admissible prob heur)
    (ret_plan : (planner_gen prob heur).isSome) :
    ∀ plan : PlanningTask.Plan prob prob.init, plan.path.cost ≥ ((planner_gen prob heur).get ret_plan).path.cost := by
  revert ret_plan
  rw [planner_gen_eq]
  intro ret_plan
  exact planner_optimal prob heur admissible ret_plan

/-- Completeness of the efficient planner (transferred from `planner_gen_complete`). -/
lemma planner_gen_fast_complete (prob : PlanningTask n) (heur : BitVec n → ℕ∞)
    (admissible : heur_admissible' prob heur) :
    planner_gen_fast prob heur = Option.none → PlanningTask.Unsolvable prob := by
  rw [planner_gen_fast_eq]
  exact planner_gen_complete prob heur admissible

/-- Optimality of the efficient planner (transferred from `planner_gen_optimal`). -/
lemma planner_gen_fast_optimal (prob : PlanningTask n) (heur : BitVec n → ℕ∞)
    (admissible : heur_admissible prob heur)
    (ret_plan : (planner_gen_fast prob heur).isSome) :
    ∀ plan : PlanningTask.Plan prob prob.init, plan.path.cost ≥ ((planner_gen_fast prob heur).get ret_plan).path.cost := by
  revert ret_plan
  rw [planner_gen_fast_eq]
  intro ret_plan
  exact planner_gen_optimal prob heur admissible ret_plan

end STRIPS