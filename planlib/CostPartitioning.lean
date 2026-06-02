import planlib.Heuristics

namespace Validator

-- P is the number of partitions
-- the partining assigns in each partition to each action a cost
abbrev cost_partitioning {n : ℕ} (prob : STRIPS n) (P : ℕ) := (p : Fin P) → (a : Fin prob.actions'.length) → ℕ

def is_valid_cost_partitioning {n : ℕ} (prob : STRIPS n) (P : ℕ) (partitioning : cost_partitioning prob P) :=
  ∀ a : Fin prob.actions'.length, ((List.finRange P).map (fun p => partitioning p a)).sum ≤ prob.actions'[a].cost

def partition_STRIPS {n P : ℕ} (prob : STRIPS n) (partitioning : cost_partitioning prob P) (p : Fin P) : STRIPS n :=
  let actions : Actions' n := prob.actions'.mapFinIdx (fun i a i_lt =>
    Action.mk a.name a.pre' a.add' a.del' (partitioning p ⟨i,i_lt⟩) )
  STRIPS.mk prob.varNames actions prob.init' prob.goal'


def partition_heuristics {n P : ℕ} (prob : STRIPS n) (partitioning : cost_partitioning prob P)
  (heurs : Fin P → STRIPS n → State' n → ℕ)
  (s : State' n) : ℕ :=
  ∑ p : Fin P, heurs p (partition_STRIPS prob partitioning p) s

open WeightedDiGraph

/-! ### Partitioning preserves graph structure -/

private lemma partition_goals_eq {n P : ℕ} (prob : STRIPS n)
    (partitioning : cost_partitioning prob P) (p : Fin P) :
    trans_of_STRIPS_goals (partition_STRIPS prob partitioning p) =
    trans_of_STRIPS_goals prob := by
  unfold trans_of_STRIPS_goals partition_STRIPS; rfl

private lemma partition_adj_of_adj {n P : ℕ} (prob : STRIPS n)
    (partitioning : cost_partitioning prob P) (p : Fin P)
    {f t : State' n} (adj : (trans_of_STRIPS prob).Adj f t) :
    (trans_of_STRIPS (partition_STRIPS prob partitioning p)).Adj f t := by
  unfold trans_of_STRIPS partition_STRIPS is_successor_state at *
  simp [applicable', is_successor'] at *
  obtain ⟨a, ha, h1, h2⟩ := adj
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
  exact ⟨i, hi, h1, h2⟩

/-! ### Walk transfer between original and partitioned graphs -/

private def transfer_walk {n P : ℕ} (prob : STRIPS n)
    (partitioning : cost_partitioning prob P) (p : Fin P)
    {f t : State' n} :
    Walk (G := trans_of_STRIPS prob) f t →
    Walk (G := trans_of_STRIPS (partition_STRIPS prob partitioning p)) f t
  | Walk.nil => Walk.nil
  | Walk.cons adj rest =>
    Walk.cons (partition_adj_of_adj prob partitioning p adj)
      (transfer_walk prob partitioning p rest)

private lemma transfer_walk_support {n P : ℕ} (prob : STRIPS n)
    (partitioning : cost_partitioning prob P) (p : Fin P)
    {f t : State' n} (w : Walk (G := trans_of_STRIPS prob) f t) :
    (transfer_walk prob partitioning p w).support = w.support := by
  induction w with
  | nil => rfl
  | cons _ _ ih => simp [transfer_walk, Walk.support, ih]

private def transfer_path {n P : ℕ} (prob : STRIPS n)
    (partitioning : cost_partitioning prob P) (p : Fin P)
    {f t : State' n} (path : (trans_of_STRIPS prob).Path f t) :
    (trans_of_STRIPS (partition_STRIPS prob partitioning p)).Path f t :=
  ⟨transfer_walk prob partitioning p path.val,
   transfer_walk_support prob partitioning p path.val ▸ path.prop⟩

/-! ### Edge cost relationships -/

/-- The cost of a transferred edge in partition p is at most `partitioning p i`
    for any action index i that achieves the transition. -/
private lemma partition_edge_cost_le_action {n P : ℕ} (prob : STRIPS n)
    (partitioning : cost_partitioning prob P) (p : Fin P)
    {f t : State' n} (adj : (trans_of_STRIPS prob).Adj f t)
    (i : Fin prob.actions'.length)
    (a_app : applicable' (prob.actions'[i.val]) f = true)
    (a_succ : is_successor' (prob.actions'[i.val]) f t = true) :
    NatGraph.edgeCost (partition_adj_of_adj prob partitioning p adj) ≤
    partitioning p i := by
  convert cost_of_le_action_cost (partition_STRIPS prob partitioning p) f t
    (prob.actions'[i] |> fun a =>
      Action.mk a.name a.pre' a.add' a.del' (partitioning p i))
    _ _ _ _ using 1
  · unfold partition_STRIPS; aesop
  · unfold partition_STRIPS; aesop
  · exact a_app
  · exact a_succ

/-- For any edge, the sum over all partitions of edge costs is bounded by the original
    edge cost. This is the key inequality that makes cost partitioning work: the valid
    partitioning constraint ensures action costs distribute across partitions. -/
private lemma partition_edge_cost_sum_le {n P : ℕ} (prob : STRIPS n)
    (partitioning : cost_partitioning prob P)
    (valid : is_valid_cost_partitioning prob P partitioning)
    {f t : State' n} (adj : (trans_of_STRIPS prob).Adj f t) :
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
private lemma partition_walk_cost_sum_le {n P : ℕ} (prob : STRIPS n)
    (partitioning : cost_partitioning prob P)
    (valid : is_valid_cost_partitioning prob P partitioning)
    {f t : State' n} (w : Walk (G := trans_of_STRIPS prob) f t) :
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
lemma partition_heuristics_admissible {n P : ℕ} (prob : STRIPS n)
    (partitioning : cost_partitioning prob P)
    (heurs : Fin P → STRIPS n → State' n → ℕ)
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
      (transfer_path prob partitioning p path).cost :=
    fun p => all_admissible p v goal
      ((partition_goals_eq prob partitioning p) ▸ goal_in_goals)
      (transfer_path prob partitioning p path)
  -- Sum of heuristics ≤ sum of partition path costs ≤ original path cost
  calc ∑ p, heurs p (partition_STRIPS prob partitioning p) v
      ≤ ∑ p, (transfer_path prob partitioning p path).cost :=
        Finset.sum_le_sum (fun p _ => h_each p)
    _ ≤ path.cost := partition_walk_cost_sum_le prob partitioning valid path.val
