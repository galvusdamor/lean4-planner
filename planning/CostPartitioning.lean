import planning.Heuristics
import Mathlib.Algebra.BigOperators.Fin

namespace STRIPS

-- P is the number of partitions
-- the partining assigns in each partition to each action a cost
abbrev cost_partitioning {n : ℕ} (prob : PlanningTask n) (P : ℕ) := (p : Fin P) → (a : Fin prob.actions'.length) → ℕ

def is_valid_cost_partitioning {n : ℕ} (prob : PlanningTask n) (P : ℕ) (partitioning : cost_partitioning prob P) :=
  ∀ a : Fin prob.actions'.length, ((List.finRange P).map (fun p => partitioning p a)).sum ≤ prob.actions'[a].cost

def partition_STRIPS {n P : ℕ} (prob : PlanningTask n) (partitioning : cost_partitioning prob P) (p : Fin P) : PlanningTask n :=
  let actions : List (Action n) := prob.actions'.mapFinIdx (fun i a i_lt =>
    Action.mk a.name a.pre a.add a.del (partitioning p ⟨i,i_lt⟩) )
  PlanningTask.mk prob.varNames actions prob.init' prob.goal'

/-- Partitioning only relabels action costs, so the action list keeps its length. -/
lemma partition_STRIPS_actions_length {n P : ℕ} (prob : PlanningTask n)
    (partitioning : cost_partitioning prob P) (p : Fin P) :
    (partition_STRIPS prob partitioning p).actions'.length = prob.actions'.length := by
  unfold partition_STRIPS; simp [List.length_mapFinIdx]

/-- The cost of the `i`-th action of `partition_STRIPS prob partitioning p` is exactly the cost the
partitioning assigns to that index. -/
lemma partition_STRIPS_getElem_cost {n P : ℕ} (prob : PlanningTask n)
    (partitioning : cost_partitioning prob P) (p : Fin P) (i : ℕ)
    (hi : i < (partition_STRIPS prob partitioning p).actions'.length)
    (hi' : i < prob.actions'.length) :
    (partition_STRIPS prob partitioning p).actions'[i].cost = partitioning p ⟨i, hi'⟩ := by
  unfold partition_STRIPS
  simp [List.getElem_mapFinIdx]

/-- Partitioning only relabels action costs, so the `i`-th action keeps its preconditions, add- and
delete-effects and name. -/
lemma partition_STRIPS_getElem_fields {n P : ℕ} (prob : PlanningTask n)
    (partitioning : cost_partitioning prob P) (p : Fin P) (i : ℕ)
    (hi : i < (partition_STRIPS prob partitioning p).actions'.length)
    (hi' : i < prob.actions'.length) :
    (partition_STRIPS prob partitioning p).actions'[i].pre = prob.actions'[i].pre
    ∧ (partition_STRIPS prob partitioning p).actions'[i].add = prob.actions'[i].add
    ∧ (partition_STRIPS prob partitioning p).actions'[i].del = prob.actions'[i].del
    ∧ (partition_STRIPS prob partitioning p).actions'[i].name = prob.actions'[i].name := by
  unfold partition_STRIPS
  simp [List.getElem_mapFinIdx, Action.pre, Action.add, Action.del]

/-- Partitioning leaves the initial state and goal unchanged (only action costs are relabelled). -/
lemma partition_STRIPS_init_goal {n P : ℕ} (prob : PlanningTask n)
    (partitioning : cost_partitioning prob P) (p : Fin P) :
    (partition_STRIPS prob partitioning p).init' = prob.init'
    ∧ (partition_STRIPS prob partitioning p).goal' = prob.goal' := by
  unfold partition_STRIPS; exact ⟨rfl, rfl⟩

/-- The total cost of the actions of partition `p` is the sum of the partition's assigned costs. -/
lemma partition_STRIPS_cost_sum {n P : ℕ} (prob : PlanningTask n)
    (partitioning : cost_partitioning prob P) (p : Fin P) :
    ((partition_STRIPS prob partitioning p).actions'.map (fun a => a.cost)).sum
      = ∑ i : Fin prob.actions'.length, partitioning p i := by
  unfold partition_STRIPS
  simp only [List.mapFinIdx_eq_ofFn, List.map_ofFn, List.sum_ofFn, Function.comp, Fin.eta]

/-- The total cost of a problem's actions as a sum over action indices. -/
lemma actions_cost_sum_eq {n : ℕ} (prob : PlanningTask n) :
    (prob.actions'.map (fun a => a.cost)).sum
      = ∑ i : Fin prob.actions'.length, prob.actions'[i].cost := by
  conv_lhs => rw [← List.ofFn_getElem (xs := prob.actions')]
  rw [List.map_ofFn, List.sum_ofFn]
  rfl

/-- Change the cost of an action `a` to the cost the cost partitioning assigns to it in partition
`p`.  The relevant cost is found by locating the index of `a` in `prob.actions'`; an action that
does not occur in `prob.actions'` is returned unchanged.  This is exactly the cost that
`partition_STRIPS prob partitioning p` gives to the action, so adapting a landmark's actions makes
them genuine actions of the partitioned problem. -/
def adapt_cost_of_action_to_partition {n P : ℕ} (prob : PlanningTask n)
    (partitioning : cost_partitioning prob P) (p : Fin P) (a : Action n) : Action n :=
  if h : prob.actions'.idxOf a < prob.actions'.length then
    Action.mk a.name a.pre a.add a.del (partitioning p ⟨prob.actions'.idxOf a, h⟩)
  else a

/-- Adapting an action of `prob` to a partition keeps its name, preconditions, add- and
delete-effects; only the cost changes. -/
lemma adapt_cost_of_action_to_partition_fields {n P : ℕ} (prob : PlanningTask n)
    (partitioning : cost_partitioning prob P) (p : Fin P) (a : Action n) :
    (adapt_cost_of_action_to_partition prob partitioning p a).name = a.name ∧
    (adapt_cost_of_action_to_partition prob partitioning p a).pre = a.pre ∧
    (adapt_cost_of_action_to_partition prob partitioning p a).add = a.add ∧
    (adapt_cost_of_action_to_partition prob partitioning p a).del = a.del := by
  unfold adapt_cost_of_action_to_partition; split <;>
    simp [Action.pre, Action.add, Action.del]

/-- The cost assigned to an adapted action of `prob` is the partition value at its index. -/
lemma adapt_cost_of_action_to_partition_cost {n P : ℕ} (prob : PlanningTask n)
    (partitioning : cost_partitioning prob P) (p : Fin P) (a : Action n)
    (ha : a ∈ prob.actions') :
    (adapt_cost_of_action_to_partition prob partitioning p a).cost
      = partitioning p ⟨prob.actions'.idxOf a, List.idxOf_lt_length_of_mem ha⟩ := by
  unfold adapt_cost_of_action_to_partition
  rw [dif_pos (List.idxOf_lt_length_of_mem ha)]

/-- An adapted action of `prob` is the action that `partition_STRIPS prob partitioning p` puts at
the (first) index of `a`, hence it is a genuine action of the partitioned problem. -/
lemma adapt_cost_of_action_to_partition_mem {n P : ℕ} (prob : PlanningTask n)
    (partitioning : cost_partitioning prob P) (p : Fin P) (a : Action n)
    (ha : a ∈ prob.actions') :
    adapt_cost_of_action_to_partition prob partitioning p a
      ∈ (partition_STRIPS prob partitioning p).actions' := by
  have hlt : prob.actions'.idxOf a < prob.actions'.length := List.idxOf_lt_length_of_mem ha
  have hget : prob.actions'[prob.actions'.idxOf a] = a := List.getElem_idxOf hlt
  have hlt' : prob.actions'.idxOf a < (partition_STRIPS prob partitioning p).actions'.length := by
    rw [partition_STRIPS_actions_length]; exact hlt
  rw [List.mem_iff_getElem]
  refine ⟨prob.actions'.idxOf a, hlt', ?_⟩
  unfold partition_STRIPS adapt_cost_of_action_to_partition
  rw [dif_pos hlt]
  rw [List.getElem_mapFinIdx]
  simp only [hget]


def partition_heuristics {n P : ℕ} (prob : PlanningTask n) (partitioning : cost_partitioning prob P)
  (heurs : Fin P → PlanningTask n → BitVec n → ℕ∞)
  (s : BitVec n) : ℕ∞ :=
  ∑ p : Fin P, heurs p (partition_STRIPS prob partitioning p) s

open WeightedDiGraph

/-! ### Partitioning preserves graph structure -/

private lemma partition_goals_eq {n P : ℕ} (prob : PlanningTask n)
    (partitioning : cost_partitioning prob P) (p : Fin P) :
    trans_of_STRIPS_goals (partition_STRIPS prob partitioning p) =
    trans_of_STRIPS_goals prob := by
  unfold trans_of_STRIPS_goals partition_STRIPS; rfl

private lemma partition_adj_of_adj {n P : ℕ} (prob : PlanningTask n)
    (partitioning : cost_partitioning prob P) (p : Fin P)
    {f t : BitVec n} (adj : (trans_of_STRIPS prob).Adj f t) :
    (trans_of_STRIPS (partition_STRIPS prob partitioning p)).Adj f t := by
  unfold trans_of_STRIPS partition_STRIPS is_successor_state at *
  simp [applicable', is_successor'] at *
  obtain ⟨a, ha, h1, h2⟩ := adj
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
  exact ⟨i, hi, h1, h2⟩

/-! ### Walk transfer between original and partitioned graphs -/

private def transfer_walk {n P : ℕ} (prob : PlanningTask n)
    (partitioning : cost_partitioning prob P) (p : Fin P)
    {f t : BitVec n} :
    Walk (G := trans_of_STRIPS prob) f t →
    Walk (G := trans_of_STRIPS (partition_STRIPS prob partitioning p)) f t
  | Walk.nil => Walk.nil
  | Walk.cons adj rest =>
    Walk.cons (partition_adj_of_adj prob partitioning p adj)
      (transfer_walk prob partitioning p rest)

private lemma transfer_walk_support {n P : ℕ} (prob : PlanningTask n)
    (partitioning : cost_partitioning prob P) (p : Fin P)
    {f t : BitVec n} (w : Walk (G := trans_of_STRIPS prob) f t) :
    (transfer_walk prob partitioning p w).support = w.support := by
  induction w with
  | nil => rfl
  | cons _ _ ih => simp [transfer_walk, Walk.support, ih]

private def transfer_path {n P : ℕ} (prob : PlanningTask n)
    (partitioning : cost_partitioning prob P) (p : Fin P)
    {f t : BitVec n} (path : (trans_of_STRIPS prob).Path f t) :
    (trans_of_STRIPS (partition_STRIPS prob partitioning p)).Path f t :=
  ⟨transfer_walk prob partitioning p path.val,
   transfer_walk_support prob partitioning p path.val ▸ path.prop⟩

/-! ### Edge cost relationships -/

/-
The cost of a transferred edge in partition p is at most `partitioning p i`
    for any action index i that achieves the transition.
-/
private lemma partition_edge_cost_le_action {n P : ℕ} (prob : PlanningTask n)
    (partitioning : cost_partitioning prob P) (p : Fin P)
    {f t : BitVec n} (adj : (trans_of_STRIPS prob).Adj f t)
    (i : Fin prob.actions'.length)
    (a_app : applicable' (prob.actions'[i.val]) f = true)
    (a_succ : is_successor' (prob.actions'[i.val]) f t = true) :
    NatGraph.edgeCost (partition_adj_of_adj prob partitioning p adj) ≤
    partitioning p i := by
      have h_adj_trans : (trans_of_STRIPS (partition_STRIPS prob partitioning p)).Adj f t := by
        exact partition_adj_of_adj prob partitioning p adj;
      have h_adj_trans_cost : NatGraph.edgeCost h_adj_trans = cost_of (partition_STRIPS prob partitioning p) f t (is_successor_state_of_trans_STRIPS_adj (partition_STRIPS prob partitioning p) f t h_adj_trans) := by
        convert trans_of_STRIPS_edgeCost ( partition_STRIPS prob partitioning p ) f t h_adj_trans using 1;
      let ap : Action n := Action.mk prob.actions'[i].name prob.actions'[i].pre
        prob.actions'[i].add prob.actions'[i].del (partitioning p i)
      have hapmem : ap ∈ (partition_STRIPS prob partitioning p).actions' := by
        unfold ap partition_STRIPS
        rw [List.mem_mapFinIdx]
        refine ⟨i.val, i.isLt, ?_⟩
        simp [Action.pre, Action.add, Action.del]
      have hapapp : applicable' ap f = true := by
        change applicable' prob.actions'[i.val] f = true
        exact a_app
      have hapsucc : is_successor' ap f t = true := by
        change is_successor' prob.actions'[i.val] f t = true
        exact a_succ
      have hc := cost_of_le_action_cost (partition_STRIPS prob partitioning p) f t ap
        (is_successor_state_of_trans_STRIPS_adj (partition_STRIPS prob partitioning p) f t h_adj_trans)
        hapmem hapapp hapsucc
      exact h_adj_trans_cost.le.trans hc

private lemma partition_edge_cost_sum_le {n P : ℕ} (prob : PlanningTask n)
    (partitioning : cost_partitioning prob P)
    (valid : is_valid_cost_partitioning prob P partitioning)
    {f t : BitVec n} (adj : (trans_of_STRIPS prob).Adj f t) :
    ∑ p : Fin P, NatGraph.edgeCost (partition_adj_of_adj prob partitioning p adj) ≤
    NatGraph.edgeCost adj := by
  -- Find the minimum-cost action achieving the transition
  have is_succ := is_successor_state_of_trans_STRIPS_adj prob f t adj
  set a_star := min_cost_action prob f t is_succ with ha_star_def
  have ha_mem := min_cost_action_in_prob prob f t is_succ
  have ha_app := successor_implies_applicable (min_cost_action_creates_successor prob f t adj)
  have ha_succ := successor_implies_is_successor (min_cost_action_creates_successor prob f t adj)
  have ha_cost := min_cost_action_cost_eq_cost_of prob f t is_succ
  -- Get the index of a_star in prob.actions'
  obtain ⟨idx, hidx, heq⟩ := List.mem_iff_getElem.mp ha_mem
  set i := (⟨idx, hidx⟩ : Fin prob.actions'.length)
  -- Each partition's edge cost is ≤ partitioning p i
  have h_le_part : ∀ p : Fin P,
      NatGraph.edgeCost (partition_adj_of_adj prob partitioning p adj) ≤
      partitioning p i :=
    fun p => partition_edge_cost_le_action prob partitioning p adj i
      (heq ▸ ha_app) (heq ▸ ha_succ)
  -- Sum over partitions ≤ sum of partitioning values ≤ action cost = edge cost
  calc ∑ p, NatGraph.edgeCost (partition_adj_of_adj prob partitioning p adj)
      ≤ ∑ p, partitioning p i := Finset.sum_le_sum (fun p _ => h_le_part p)
    _ = ((List.finRange P).map (fun p => partitioning p i)).sum := by
        simp [Finset.sum, Finset.univ, Fintype.elems]
    _ ≤ prob.actions'[i].cost := valid i
    _ = a_star.cost := congrArg Action.cost heq
    _ = cost_of prob f t is_succ := ha_cost
    _ = NatGraph.edgeCost adj := (trans_of_STRIPS_edgeCost prob f t adj).symm

/-! ### Walk cost sum inequality -/

/-- The sum of walk costs across all partitions is bounded by the original walk cost.
    Proved by induction on the walk, using `partition_edge_cost_sum_le` at each step. -/
private lemma partition_walk_cost_sum_le {n P : ℕ} (prob : PlanningTask n)
    (partitioning : cost_partitioning prob P)
    (valid : is_valid_cost_partitioning prob P partitioning)
    {f t : BitVec n} (w : Walk (G := trans_of_STRIPS prob) f t) :
    ∑ p : Fin P, (transfer_walk prob partitioning p w).cost ≤ w.cost := by
  induction w with
  | nil => simp [transfer_walk, Walk.cost]
  | cons adj rest ih =>
    simp only [transfer_walk, Walk.cost]
    calc ∑ p, (NatGraph.edgeCost (partition_adj_of_adj prob partitioning p adj) +
              (transfer_walk prob partitioning p rest).cost)
        = ∑ p, NatGraph.edgeCost (partition_adj_of_adj prob partitioning p adj) +
          ∑ p, (transfer_walk prob partitioning p rest).cost := Finset.sum_add_distrib
      _ ≤ NatGraph.edgeCost adj + rest.cost :=
          Nat.add_le_add (partition_edge_cost_sum_le prob partitioning valid adj) ih

/-! ### Main theorem -/

/-- The sum of admissible heuristics under a valid cost partitioning is itself admissible.
    Each heuristic underestimates the path cost in its partition, and the valid partitioning
    ensures that the sum of partition costs does not exceed the original path cost. -/
lemma partition_heuristics_admissible {n P : ℕ} (prob : PlanningTask n)
    (partitioning : cost_partitioning prob P)
    (heurs : Fin P → PlanningTask n → BitVec n → ℕ∞)
    (valid : is_valid_cost_partitioning prob P partitioning)
    (all_admissible : ∀ p : Fin P,
      heur_admissible' (partition_STRIPS prob partitioning p)
        (heurs p (partition_STRIPS prob partitioning p))) :
    heur_admissible' prob (partition_heuristics prob partitioning heurs) := by
  intro v goal goal_in_goals path
  unfold partition_heuristics
  -- Each heuristic is ≤ the path cost in its partition
  have h_each : ∀ p : Fin P,
      heurs p (partition_STRIPS prob partitioning p) v ≤
      ((transfer_path prob partitioning p path).cost : ℕ∞) :=
    fun p => all_admissible p v goal
      ((partition_goals_eq prob partitioning p) ▸ goal_in_goals)
      (transfer_path prob partitioning p path)
  -- Sum of heuristics ≤ sum of partition path costs ≤ original path cost
  calc ∑ p, heurs p (partition_STRIPS prob partitioning p) v
      ≤ ∑ p, ((transfer_path prob partitioning p path).cost : ℕ∞) :=
        Finset.sum_le_sum (fun p _ => h_each p)
    _ = ((∑ p, (transfer_path prob partitioning p path).cost : ℕ) : ℕ∞) := by push_cast; rfl
    _ ≤ (path.cost : ℕ∞) := by
        exact_mod_cast partition_walk_cost_sum_le prob partitioning valid path.val