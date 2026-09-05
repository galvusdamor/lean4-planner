import planning.PlannerGen

/-!
# A fact-indexed action table for state expansion

Expanding a state in the STRIPS search costs

* one scan of *all* actions to collect the applicable ones (`STRIPS.successorStates`), and
* one scan of *all* actions **per generated edge** to determine the edge cost
  (`STRIPS.cost_of`, which filters the actions by applicability and by "produces exactly this
  successor" and takes the minimum of the costs).

Measured on the shipped tasks, the per-edge cost computation dominates a state expansion by
more than an order of magnitude: with a branching factor of `k`, an expansion costs `k + 1`
full action scans.

This module removes the per-edge scan.  It precomputes, **once per task**, for every variable
the list of actions that add it and the list of actions that delete it
(`STRIPS.FactIndex`), in the order in which they occur in `prob.actions'`.  For an edge
`f → t` this immediately restricts the candidates:

* every action `a` with `successor' a f = t` adds every fact of `t \ f`, so if `t \ f` is
  nonempty the candidates are the actions that add one (fixed) such fact;
* if `t = f ∪ …` has no new fact but `f \ t` is nonempty, every such action deletes every
  fact of `f \ t`, so the deleters of one such fact are the candidates;
* otherwise (`t = f`) all actions remain candidates.

Since each bucket is a *filter of the action list*, the candidate list is a filter of
`prob.actions'`, and filtering it again by the predicate used in `cost_of` gives literally
the same list — which is why `STRIPS.cost_of_fast` is *equal* to `STRIPS.cost_of`
(`STRIPS.cost_of_fast_eq`), not merely equivalent.

The index is built in one pass over the actions (`STRIPS.mkFactIndex`) and identified with
its declarative description in `STRIPS.mkFactIndex_adders` / `STRIPS.mkFactIndex_deleters`.
-/

namespace STRIPS

variable {n : ℕ}

/-! ### Bucketing the actions by the facts they add and delete -/

/-- Prepend `a` to the buckets of all facts in `l`. -/
def bucketInsert (a : Action n) : List (Fin n) → Vector (List (Action n)) n →
    Vector (List (Action n)) n
  | [], bs => bs
  | x :: xs, bs => bucketInsert a xs (bs.set x.1 (a :: bs[x]) x.2)

/-- The buckets of a list of actions, keyed by the facts selected by `key`. -/
def buckets (key : Action n → List (Fin n)) (as : List (Action n)) :
    Vector (List (Action n)) n :=
  as.foldr (fun a bs => bucketInsert a (key a) bs) (Vector.replicate n [])

/-- The fact index of a task: for every variable, the actions that add it and the actions
that delete it. -/
structure FactIndex (n : ℕ) where
  /-- For every variable, the actions that add it, in the order of `prob.actions'`. -/
  adders : Vector (List (Action n)) n
  /-- For every variable, the actions that delete it, in the order of `prob.actions'`. -/
  deleters : Vector (List (Action n)) n

/-- The fact index of a task, built in one pass over the actions. -/
def mkFactIndex (prob : PlanningTask n) : FactIndex n where
  adders := buckets (fun a => a.add.toList) prob.actions'
  deleters := buckets (fun a => a.del.toList) prob.actions'

/-- Reading a bucket after inserting one action: the action is prepended exactly to the
buckets of the (duplicate-free) key list. -/
lemma bucketInsert_getElem (a : Action n) (l : List (Fin n)) :
    ∀ (bs : Vector (List (Action n)) n) (x : Fin n), l.Nodup →
      (bucketInsert a l bs)[x] = if x ∈ l then a :: bs[x] else bs[x] := by
  induction l with
  | nil => intro bs x _; simp [bucketInsert]
  | cons y ys ih =>
    intro bs x hl
    rw [bucketInsert, ih _ x hl.of_cons]
    by_cases hx : x = y
    · subst hx
      have hnot : x ∉ ys := (List.nodup_cons.1 hl).1
      simp [hnot, Vector.getElem_set_self]
    · have hne : (y : ℕ) ≠ (x : ℕ) := fun h => hx (Fin.ext h).symm
      by_cases hmem : x ∈ ys <;> simp [hmem, hx, Vector.getElem_set_ne _ _ hne]

/-- The buckets are the filters of the action list. -/
lemma buckets_getElem (key : Action n → List (Fin n)) (hkey : ∀ a, (key a).Nodup)
    (as : List (Action n)) (x : Fin n) :
    (buckets key as)[x] = as.filter (fun a => decide (x ∈ key a)) := by
  induction as with
  | nil => simp [buckets]
  | cons a as ih =>
    rw [buckets, List.foldr_cons, show as.foldr (fun a bs => bucketInsert a (key a) bs)
        (Vector.replicate n []) = buckets key as from rfl,
      bucketInsert_getElem a (key a) _ x (hkey a), ih, List.filter_cons]
    by_cases hx : x ∈ key a <;> simp [hx]

/-- The adders bucket of a fact is the list of actions adding it. -/
lemma mkFactIndex_adders (prob : PlanningTask n) (x : Fin n) :
    (mkFactIndex prob).adders[x] = prob.actions'.filter (fun a => decide (x ∈ a.add.toList)) :=
  buckets_getElem _ (fun a => a.add.toList_nodup) _ x

/-- The deleters bucket of a fact is the list of actions deleting it. -/
lemma mkFactIndex_deleters (prob : PlanningTask n) (x : Fin n) :
    (mkFactIndex prob).deleters[x] = prob.actions'.filter (fun a => decide (x ∈ a.del.toList)) :=
  buckets_getElem _ (fun a => a.del.toList_nodup) _ x

/-! ### The candidate actions of an edge -/

/-- Scan the bits `k-1, …, 0` of `v` downwards for a set bit. -/
def firstSetBitAux (v : BitVec n) : (k : ℕ) → k ≤ n → Option (Fin n)
  | 0, _ => none
  | k + 1, h =>
      if v[k]'(by omega) then some ⟨k, by omega⟩ else firstSetBitAux v k (by omega)

/-- The index of some set bit of a bit vector, if there is one.  (No list is allocated: the
bits are scanned downwards and the scan stops at the first set bit.) -/
def firstSetBit (v : BitVec n) : Option (Fin n) := firstSetBitAux v n le_rfl

lemma firstSetBitAux_spec {v : BitVec n} : ∀ (k : ℕ) (hk : k ≤ n) {i : Fin n},
    firstSetBitAux v k hk = some i → v[i.1] = true := by
  intro k
  induction k with
  | zero => intro _ i h; simp [firstSetBitAux] at h
  | succ k ih =>
    intro hk i h
    rw [firstSetBitAux] at h
    split at h
    · rename_i hv
      rw [Option.some.injEq] at h
      subst h
      exact hv
    · exact ih _ h

lemma firstSetBit_spec {v : BitVec n} {i : Fin n} (h : firstSetBit v = some i) :
    v[i.1] = true :=
  firstSetBitAux_spec n le_rfl h

/-- The actions that can produce the edge `f → t`: if `t` has a fact that `f` does not
have, the actions adding that fact; otherwise, if `f` has a fact that `t` does not have, the
actions deleting that fact; otherwise all actions. -/
def edgeCandidates (idx : FactIndex n) (prob : PlanningTask n) (f t : BitVec n) :
    List (Action n) :=
  match firstSetBit (t &&& ~~~f) with
  | some x => idx.adders[x]
  | none =>
    match firstSetBit (f &&& ~~~t) with
    | some x => idx.deleters[x]
    | none => prob.actions'

/-- The predicate that `cost_of` filters the actions by. -/
def edgeAction (f t : BitVec n) (a : Action n) : Bool :=
  applicable' a f && is_successor' a f t

/-- Every action that realises the edge `f → t` adds every fact of `t \ f` and deletes every
fact of `f \ t`. -/
lemma edgeAction_mem_add {f t : BitVec n} {a : Action n} (h : edgeAction f t a = true)
    {x : Fin n} (hx : (t &&& ~~~f)[x.1] = true) : x ∈ a.add.toList := by
  simp only [edgeAction, Bool.and_eq_true, is_successor', decide_eq_true_eq] at h
  obtain ⟨-, rfl⟩ := h
  simp only [successor', BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_or,
    Bool.and_eq_true, Bool.or_eq_true] at hx
  simp only [VarSet.mem_toList, VarSet.mem_val, VarSet.mem_iff]
  rcases hx with ⟨h1 | h2, hf⟩
  · simp [h1.1] at hf
  · exact h2

lemma edgeAction_mem_del {f t : BitVec n} {a : Action n} (h : edgeAction f t a = true)
    {x : Fin n} (hx : (f &&& ~~~t)[x.1] = true) : x ∈ a.del.toList := by
  simp only [edgeAction, Bool.and_eq_true, is_successor', decide_eq_true_eq] at h
  obtain ⟨-, rfl⟩ := h
  simp only [successor', BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_or,
    Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff] at hx
  simp only [VarSet.mem_toList, VarSet.mem_val, VarSet.mem_iff]
  obtain ⟨hf, h1, h2⟩ := hx
  simpa [hf] using h1

/-- Filtering the candidates of an edge by `edgeAction` gives the same list as filtering all
actions: the candidate list is a filter of the action list that keeps every action realising
the edge. -/
theorem filter_edgeCandidates (prob : PlanningTask n) (f t : BitVec n) :
    (edgeCandidates (mkFactIndex prob) prob f t).filter (edgeAction f t)
      = prob.actions'.filter (edgeAction f t) := by
  unfold edgeCandidates
  cases hadd : firstSetBit (t &&& ~~~f) with
  | some x =>
    show ((mkFactIndex prob).adders[x]).filter (edgeAction f t) = _
    rw [mkFactIndex_adders, List.filter_filter]
    refine (List.filter_congr ?_).symm
    intro a _
    by_cases h : edgeAction f t a = true
    · simp [h, edgeAction_mem_add h (firstSetBit_spec hadd)]
    · simp only [Bool.not_eq_true] at h
      simp [h]
  | none =>
    cases hdel : firstSetBit (f &&& ~~~t) with
    | some x =>
      show ((mkFactIndex prob).deleters[x]).filter (edgeAction f t) = _
      rw [mkFactIndex_deleters, List.filter_filter]
      refine (List.filter_congr ?_).symm
      intro a _
      by_cases h : edgeAction f t a = true
      · simp [h, edgeAction_mem_del h (firstSetBit_spec hdel)]
      · simp only [Bool.not_eq_true] at h
        simp [h]
    | none => rfl

/-! ### The edge cost, computed from the index -/

/-- The filter predicate of `cost_of` is `edgeAction`. -/
lemma filter_edgeAction_eq (prob : PlanningTask n) (f t : BitVec n) :
    prob.actions'.filter (fun a => decide (applicable' a f ∧ is_successor' a f t))
      = prob.actions'.filter (edgeAction f t) := by
  refine List.filter_congr ?_
  intro a _
  simp [edgeAction]

/-- **The edge cost computed from the fact index.**  Only the actions that add (or delete) a
fact on which `f` and `t` differ are examined; by `filter_edgeCandidates` these are exactly
the actions that `cost_of` keeps. -/
def cost_of_fast (prob : PlanningTask n) (idx : FactIndex n) (hidx : idx = mkFactIndex prob)
    (f t : BitVec n) (is_succ : is_successor_state prob f t) : ℕ :=
  (((edgeCandidates idx prob f t).filter (edgeAction f t)).map (fun a => a.cost)).min (by
    subst hidx
    rw [filter_edgeCandidates, ← filter_edgeAction_eq]
    simp_all)

/-- **The fast edge cost is the edge cost.** -/
theorem cost_of_fast_eq (prob : PlanningTask n) (idx : FactIndex n)
    (hidx : idx = mkFactIndex prob) (f t : BitVec n)
    (is_succ : is_successor_state prob f t) :
    cost_of_fast prob idx hidx f t is_succ = cost_of prob f t is_succ := by
  subst hidx
  unfold cost_of_fast cost_of
  congr 1
  rw [filter_edgeCandidates, ← filter_edgeAction_eq]

end STRIPS
