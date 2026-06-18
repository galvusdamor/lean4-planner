import planning.LMCutHeuristic
import planning.H1

/-!
# An `h_1`-based precondition-choice function for LM-cut

This file constructs a concrete precondition-choice function (pcf) for the LM-cut heuristic:
for every action, it computes, for each of the action's preconditions individually (taking that
single fact as the goal), the value of the `h_1` heuristic, and then chooses the precondition with
the **largest** `h_1` value (the "`h_1`/`h^max` maximiser").

With this maximiser pcf, LM-cut dominates `h_1`: for every solvable state `s`,
`lmcut prob s h1_pcf ≥ h_1 prob s`.

This is the classical result that `h^{LM-cut}` dominates `h^max` (here `h_1 = h^max`), specialised
to the maximiser precondition-choice function.

## Main results

* `h1_pcf` — the maximiser precondition-choice function.
* `h1_goal_value_step_bound` — the Helmert–Domshlak per-step property: in one LM-cut step `h^max`
  of the goal decreases by at most the cut value `minCost`.
* `h1_goal_value_le_of_walk`, `h1_goal_value_walk_lb`, `h1_goal_value_eq_walk_cost` — the
  `h^max`–justification-graph correspondence: the upper bound of `h^max` along any maximiser-graph
  walk, the achievability of `h^max` by some walk, and their equality form.
* `h1_goal_value_eq_fixpoint` — identifies `h1_goal_value` with the `h^max` fixpoint vector entry.

The achievability argument relies on the value-stabilisation rank theory in `planning.H1`
(`h_1_rank`, `h_1_rank_attained`, and the Bellman characterisations of `h_1_step`).
-/

namespace Validator

open List

/-- The singleton variable set `{f}` (always strictly sorted). -/
def singletonVarSet {m : ℕ} (f : Fin m) : VarSet' m :=
  ⟨[f], by simp [List.SortedLT, StrictMono]⟩

/-- The `h_1` value of reaching a single fact `f` from the initial state of `p`, i.e. `h_1` of the
problem `p` with its goal replaced by the singleton goal `{f}`. -/
def h1_goal_value {m : ℕ} (p : STRIPS m) (f : Fin m) : ℕ :=
  h_1 (replace_goal p (singletonVarSet f)) p.init'

/-- The fact of `a`'s preconditions with the largest `h_1` value (taking that fact as the goal).
Requires that `a` has at least one precondition (`hne`). -/
def h1_argmax_pre {m : ℕ} (p : STRIPS m) (a : Action m) (hne : a.pre'.val ≠ []) : Fin m :=
  (a.pre'.val.argmax (fun f => h1_goal_value p f)).get (by
    rw [Option.isSome_iff_ne_none]
    intro h
    exact hne (List.argmax_eq_none.mp h))

/-- `h1_argmax_pre` is one of `a`'s preconditions. -/
lemma h1_argmax_pre_mem {m : ℕ} (p : STRIPS m) (a : Action m) (hne : a.pre'.val ≠ []) :
    h1_argmax_pre p a hne ∈ a.pre'.val :=
  List.argmax_mem (Option.get_mem _)

/-- `h1_argmax_pre` maximises the `h_1` value over all of `a`'s preconditions. -/
lemma h1_argmax_pre_max {m : ℕ} (p : STRIPS m) (a : Action m) (hne : a.pre'.val ≠ [])
    {f : Fin m} (hf : f ∈ a.pre'.val) :
    h1_goal_value p f ≤ h1_goal_value p (h1_argmax_pre p a hne) :=
  List.le_of_mem_argmax hf (Option.get_mem _)

/-- **The `h_1`-maximiser precondition-choice function.**

For every problem `p` (with preconditions) and every action `a`, it chooses the precondition of `a`
with the largest `h_1` value, computed by taking that single precondition fact as the goal. -/
def h1_pcf {n : ℕ} :
    Π p : STRIPS (n + 2), has_preconditions p → precondition_choice_function p :=
  fun p hp a =>
    ⟨h1_argmax_pre p a.val (hp a.val a.property),
      mem_pre_of_mem_pre'_val a.val (h1_argmax_pre_mem p a.val (hp a.val a.property))⟩

/-! ### Domination of `h_1` by LM-cut with the `h_1`-maximiser pcf

The proof follows the classical argument that `h^{LM-cut}` dominates `h^max` (here `h_1 = h^max`),
specialised to the `h_1`-maximiser precondition-choice function.  It is organised around the
recursion of `lmcut_inner`:

* `h1_goal_value p (goal fact)` is exactly `h^max` of the (unitary) goal fact of `p` (it is defined
  by the `h_1` fixpoint and does **not** depend on the pcf)
* in the zero-cost-reachable base case, `h^max` of the goal is `0` (`h1_goal_value_zero`)
* in the recursive step, `h^max` of the goal decreases by **at most** the cut value `minCost` when
  the cut actions are made cheaper (`h1_goal_value_step_bound`, the Helmert–Domshlak property)
* therefore, by strong induction on the total action cost, the accumulated LM-cut value dominates
  `h^max` of the goal (`lmcut_inner_ge_h1_goal`)
* finally, `h^max` of the goal fact of the i/g normal form equals the original `h_1` value
  (`h1_goal_value_normal_form`), which yields the theorem. -/

/-- A fact that is already satisfied in the initial state has `h_1`/`h^max` value `0`. -/
lemma h1_goal_value_eq_zero_of_satisfies {m : ℕ} (p : STRIPS m) (f : Fin m)
    (hf : satisfies' (singletonVarSet f) p.init' = true) :
    h1_goal_value p f = 0 := by
  unfold h1_goal_value
  exact h_1_goal_aware p (singletonVarSet f) p.init' hf

/-
The unitary initial fact has `h_1`/`h^max` value `0`.
-/
lemma h1_goal_value_init_zero {m : ℕ} (p : STRIPS m) (u_i : unitary_init p) :
    h1_goal_value p (get_unitary_init p u_i) = 0 := by
  convert h_1_goal_aware p ( singletonVarSet ( get_unitary_init p u_i ) ) p.init' _
  convert get_unitary_init_is_init p u_i
  unfold satisfies' singletonVarSet
  simp +decide [ STRIPS.init, convertState ]
  constructor <;> intro h
  · convert get_unitary_init_is_init p u_i
  · exact h.symm.subset rfl

/-
Regressing the singleton add-fact `{t}` (with `t ∈ a.add'`) through `a` yields exactly the
precondition facts of `a`: any fact in the regressed goal is a precondition of `a`.
-/
lemma mem_pre_of_mem_regress_add {m : ℕ} (a : Action m) (t : Fin m) (ht : t ∈ a.add'.val)
    {g' : Fin m}
    (hg' : g' ∈ (varset'_of_state' (regress' a (state'_of_varset' (singletonVarSet t)))).val) :
    g' ∈ a.pre'.val := by
  unfold varset'_of_state' at hg'
  unfold regress' at hg'; simp +decide [ singletonVarSet ] at hg'
  contrapose! hg'
  rw [ BitVec.getElem_ofBoolListLE ] ; simp +decide [ hg', ht ]
  grind +suggestions

/-
**Bellman bound for the maximiser.** The `h_1`/`h^max` value of an add-fact `t` of an action `a`
is at most `a.cost` plus the `h_1`/`h^max` value of `a`'s `h_1`-maximiser precondition.  This is the
one-step `h^max` recursion, using that the `h_1`-maximiser precondition dominates all of `a`'s
preconditions.
-/
lemma h1_goal_value_bellman_argmax {m : ℕ} (p : STRIPS m) (a : Action m) (ha : a ∈ p.actions')
    (hne : a.pre'.val ≠ []) (t : Fin m) (ht : t ∈ a.add'.val) :
    h1_goal_value p t ≤ a.cost + h1_goal_value p (h1_argmax_pre p a hne) := by
  have h_regressed_le_max : ∀ g' ∈ (varset'_of_state' (regress' a (state'_of_varset' (singletonVarSet t)))).val, h1_goal_value p g' ≤ h1_goal_value p (h1_argmax_pre p a hne) := by
    exact fun g' hg' => h1_argmax_pre_max p a hne <| mem_pre_of_mem_regress_add a t ht hg'
  have h_regressed_le_max : h_1 (replace_goal p (varset'_of_state' (regress' a (state'_of_varset' (singletonVarSet t)))) ) p.init' ≤ h1_goal_value p (h1_argmax_pre p a hne) := by
    cases' e : ( varset'_of_state' ( regress' a ( state'_of_varset' ( singletonVarSet t ) ) ) ).val with g' rg'
    · unfold h_1; simp +decide [ e ] 
      unfold replace_goal; simp +decide [ e ] 
      unfold satisfies'; simp +decide [ e ] 
    · by_cases hlen : rg'.length > 0
      · have := h_1_multi_atom p ( varset'_of_state' ( regress' a ( state'_of_varset' ( singletonVarSet t ) ) ) ) p.init' ( by
          grind )
        refine le_trans this ?_
        rw [ List.max_le_iff ]
        simp +zetaDelta at *
        exact fun x hx => h_regressed_le_max x hx
      · cases rg' <;> simp_all +decide
        convert h_regressed_le_max using 1
        congr
        exact Subtype.ext e
  convert le_trans _ ( add_le_add_left h_regressed_le_max a.cost ) using 1
  · ring
  · have := h_1_singleton_bellman_add p t p.init' a ha ht
    convert this using 1 ; ring!

/-
A zero-cost edge of the justification graph is witnessed by a zero-cost action whose chosen
precondition is the source and whose add effect contains the target.
-/
lemma jgraph_zero_cost_edge_witness {n : ℕ} (p : STRIPS (n + 2)) (hp : has_preconditions p)
    {f t : Fin (n + 2)} (adj : (justification_graph p (h1_pcf p hp)).Adj f t)
    (h0 : (justification_graph p (h1_pcf p hp)).Payload f t adj = 0) :
    ∃ a : {b : Action (n + 2) // b ∈ p.actions'},
      (↑(h1_pcf p hp a) : Fin (n + 2)) = f ∧ t ∈ a.val.add'.val.toFinset ∧ a.val.cost = 0 := by
  obtain ⟨a, ha₁, ha₂, ha₃⟩ : ∃ a : {a : Action (n + 2) // a ∈ p.actions'},
      (↑(h1_pcf p hp a) : Fin (n + 2)) = f ∧ t ∈ a.val.add'.val.toFinset ∧
        a.val.cost = (justification_graph p (h1_pcf p hp)).Payload f t adj := by
    unfold justification_graph at *
    grind +suggestions
  exact ⟨a, ha₁, ha₂, by rw [ha₃, h0]⟩

/-
Propagation of `h1_goal_value = 0` along a zero-cost walk of the justification graph.
-/
lemma h1_goal_value_zero_of_zero_walk {n : ℕ} (p : STRIPS (n + 2)) (hp : has_preconditions p)
    {v w : Fin (n + 2)} (walk : (justification_graph p (h1_pcf p hp)).Walk v w)
    (hcost : walk.cost = 0) (hv : h1_goal_value p v = 0) :
    h1_goal_value p w = 0 := by
  induction' walk with v w a h ih
  · exact hv
  · have h_edge_cost_zero : (justification_graph p (h1_pcf p hp)).Payload w a ih = 0 := by
      unfold WeightedDiGraph.Walk.cost at hcost
      unfold NatGraph.edgeCost at hcost
      simp_all only [Nat.add_eq_zero_iff]
    have h_a_zero : h1_goal_value p a = 0 := by
      have := jgraph_zero_cost_edge_witness p hp ih h_edge_cost_zero
      obtain ⟨ a, ha₁, ha₂, ha₃ ⟩ := this
      have := h1_goal_value_bellman_argmax p a.val a.property ( hp a.val a.property ) _ ( List.mem_toFinset.mp ha₂ ) ; simp_all +decide [ h1_pcf ] 
    unfold WeightedDiGraph.Walk.cost at hcost
    simp_all only [forall_const, Nat.add_eq_zero_iff]

/-
**Per-edge propagation bound.** For an edge `f → t` of the maximiser justification graph, the
`h^max` value of `t` is at most the edge payload plus the `h^max` value of `f`.  The payload is the
minimum cost over actions whose chosen precondition is `f` and whose add effect contains `t`; the
minimiser `a*` has `h1_pcf` choice equal to `f`, so the one-step Bellman bound
`h1_goal_value_bellman_argmax` applied to `a*` yields the claim.
-/
lemma h1_goal_value_edge_bound {n : ℕ} (p : STRIPS (n + 2)) (hp : has_preconditions p)
    {f t : Fin (n + 2)} (adj : (justification_graph p (h1_pcf p hp)).Adj f t) :
    h1_goal_value p t
      ≤ (justification_graph p (h1_pcf p hp)).Payload f t adj + h1_goal_value p f := by
  obtain ⟨a, ha₁, ha₂, ha₃⟩ : ∃ a : {a : Action (n + 2) // a ∈ p.actions'}, (↑(h1_pcf p hp a) : Fin (n + 2)) = f ∧ t ∈ a.val.add'.val.toFinset ∧ a.val.cost = (justification_graph p (h1_pcf p hp)).Payload f t adj := by
    unfold justification_graph at *
    grind +suggestions
  have := h1_goal_value_bellman_argmax p a.val a.property ( hp a.val a.property ) t ( by simpa using ha₂ ) ; simp_all +decide [ h1_pcf ] 

/-
**Generalized propagation along a walk.** Along a justification-graph walk from `v` to `w`, the
`h^max` value of `w` exceeds that of `v` by at most the walk cost.  Proved by induction on the walk,
using `h1_goal_value_edge_bound` at each step (this generalizes `h1_goal_value_zero_of_zero_walk`).
-/
lemma h1_goal_value_le_of_walk {n : ℕ} (p : STRIPS (n + 2)) (hp : has_preconditions p)
    {v w : Fin (n + 2)} (walk : (justification_graph p (h1_pcf p hp)).Walk v w) :
    h1_goal_value p w ≤ h1_goal_value p v + walk.cost := by
  induction' walk with v w a h ih
  · exact Nat.le_add_right _ _
  · unfold WeightedDiGraph.Walk.cost
    linarith! [ h1_goal_value_edge_bound p hp ih ]

/-- **(K1)** If the goal fact is reachable using only zero-cost edges of the justification graph,
then the `h_1`/`h^max` value of the goal is `0`. -/
lemma h1_goal_value_zero {n : ℕ} (p : STRIPS (n + 2)) (u_i : unitary_init p) (u_g : unitary_goal p)
    (hp : has_preconditions p)
    (hz : zero_cost_reachable (justification_graph p (h1_pcf p hp))
      (get_unitary_init p u_i) (get_unitary_goal p u_g)) :
    h1_goal_value p (get_unitary_goal p u_g) = 0 := by
  obtain ⟨walk, hwalk⟩ := walk_of_zero_cost_reachable (justification_graph p (h1_pcf p hp)) hz
  exact h1_goal_value_zero_of_zero_walk p hp walk hwalk (h1_goal_value_init_zero p u_i)

/-
**Bridge: `h1_goal_value` is the fixpoint value.** For a fact `w` that is discovered at the
`h_1` fixpoint (its value is `isSome`), the `h^max` value `h1_goal_value p w` equals exactly that
fixpoint entry.  This is the per-fact specialisation of the computation inside `h_1`, using that the
singleton goal `{w}` does not change the fixpoint (`h_1_iter_fix_replace_goal`).
-/
lemma h1_goal_value_eq_fixpoint {n : ℕ} (p : STRIPS (n + 2)) (w : Fin (n + 2))
    (hw : ((h_1_iter_fix (n + 2) p (h_1_base (n + 2) p.init'))[w]).isSome) :
    (h_1_iter_fix (n + 2) p (h_1_base (n + 2) p.init'))[w] = some (h1_goal_value p w) := by
  unfold h1_goal_value
  unfold h_1
  simp +decide [ h_1_iter_fix_replace_goal, vec_to_state_getElem, satisfies'_singleton ]
  split_ifs <;> simp_all +decide [ replace_goal, singletonVarSet ]
  · simp +decide [ List.max ]
  · unfold satisfies' at *; simp_all +decide [ vec_to_state_getElem ] 

/-- On `WithTop ℕ`, `getD 0` is monotone when the larger value is finite. -/
theorem withTop_getD_le_getD {a b : WithTop ℕ} (hab : a ≤ b) (hb : b.isSome) :
    a.getD 0 ≤ b.getD 0 := by
  obtain ⟨y, rfl⟩ := Option.isSome_iff_exists.mp hb
  obtain ⟨x, rfl⟩ : ∃ x : ℕ, a = some x := by
    cases a with
    | top => exact absurd hab (by simp)
    | coe x => exact ⟨x, rfl⟩
  simpa using (WithTop.coe_le_coe.mp hab)

/-- Two finite `WithTop ℕ` values with equal `getD 0` are equal. -/
theorem withTop_eq_of_getD_eq {a b : WithTop ℕ} (ha : a.isSome) (hb : b.isSome)
    (h : a.getD 0 = b.getD 0) : a = b := by
  obtain ⟨x, rfl⟩ := Option.isSome_iff_exists.mp ha
  obtain ⟨y, rfl⟩ := Option.isSome_iff_exists.mp hb
  simp only [Option.getD_some] at h
  exact congrArg _ h

/-
The maximiser precondition `h1_argmax_pre` realises the maximum `h1_goal_value` over the
precondition list (as a `foldl max`).
-/
lemma h1_argmax_pre_foldl_max {n : ℕ} (p : STRIPS n) (a : Action n) (hne : a.pre'.val ≠ []) :
    (a.pre'.val.map (fun j => h1_goal_value p j)).foldl max 0
      = h1_goal_value p (h1_argmax_pre p a hne) := by
  refine' le_antisymm _ _
  · have h_foldl_le : ∀ (L : List ℕ) (b : ℕ), (∀ x ∈ L, x ≤ b) → 0 ≤ b → List.foldl max 0 L ≤ b := by
      intro L
      induction' L using List.reverseRecOn with L x ih
      · intro b _ hb; simp [hb]
      · intro b hL hb
        rw [List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil]
        exact max_le (ih b (fun y hy => hL y (List.mem_append_left _ hy)) hb)
          (hL x (List.mem_append_right _ (by simp)))
    exact h_foldl_le _ _ ( fun x hx => by obtain ⟨ j, hj, rfl ⟩ := List.mem_map.mp hx; exact h1_argmax_pre_max p a hne hj ) ( Nat.zero_le _ )
  · have h_max_le : ∀ {l : List ℕ}, ∀ x ∈ l, x ≤ List.foldl max 0 l := by
      intro l
      induction' l using List.reverseRecOn with l y ih
      · intro x hx; simp at hx
      · intro x hx
        rw [List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil]
        rcases List.mem_append.mp hx with h | h
        · exact le_trans (ih x h) (le_max_left _ _)
        · simp only [List.mem_singleton] at h; subst h; exact le_max_right _ _
    exact h_max_le _ ( List.mem_map.mpr ⟨ _, h1_argmax_pre_mem p a hne, rfl ⟩ )

/-
For an edge `f → t` of the justification graph witnessed by an action `a` (whose chosen
precondition is `f` and which adds `t`), the edge payload is at most `a`'s cost (it is the minimum
cost over all such actions).
-/
lemma justification_graph_payload_le {n : ℕ} (prob : STRIPS n)
    (pcf : precondition_choice_function prob) {f t : Fin n}
    (adj : (justification_graph prob pcf).Adj f t)
    (a : {b : Action n // b ∈ prob.actions'}) (hf : (↑(pcf a) : Fin n) = f)
    (ht : t ∈ a.val.add'.val.toFinset) :
    (justification_graph prob pcf).Payload f t adj ≤ a.val.cost := by
  convert List.min_le_of_mem _
  · infer_instance
  · infer_instance
  · grind

/-
**Achievability / lower-bound half of the `h^max`–justification-graph correspondence.** Every
fact `w` discovered at the `h_1` fixpoint is reached from the (unitary) initial fact by a walk of the
maximiser justification graph whose cost is at most `h1_goal_value p w`.  Together with the
upper-bound half (`h1_goal_value_le_of_walk`, which gives `≥`), this shows `h^max` of any discovered
fact equals the cheapest justification-graph walk to it.

The walk is built by recursion on the **value-stabilisation rank** of `w` (the first iteration index
at which `h_1_iter` reaches the fixpoint value at `w`).  At a fact of positive rank, the value is
attained at the previous iteration by some applicable adding action `a` whose maximiser precondition
`f` is already stabilised there — so `f` has strictly smaller rank, giving a recursive walk to `f`,
which is extended by the maximiser edge `f → w` (payload `≤ a.cost`).
-/
set_option maxHeartbeats 1000000 in
lemma h1_goal_value_walk_lb {n : ℕ} (p : STRIPS (n + 2)) (hp : has_preconditions p)
    (u_i : unitary_init p) (w : Fin (n + 2))
    (hw : ((h_1_iter_fix (n + 2) p (h_1_base (n + 2) p.init'))[w]).isSome) :
    ∃ walk : (justification_graph p (h1_pcf p hp)).Walk (get_unitary_init p u_i) w,
      walk.cost ≤ h1_goal_value p w := by
  revert hw w
  intro w hw
  set base := h_1_base (n + 2) p.init'
  set Rfix := h_1_iter_fix (n + 2) p base
  set I := get_unitary_init p u_i
  induction' N : h_1_rank p base w using Nat.strong_induction_on with N ih generalizing w
  by_cases hw0 : h_1_rank p base w = 0
  · have hw_eq_I : p.init'[w] = true := by
      have hw_eq_I : Rfix[w] = base[w] := by
        have := h_1_rank_spec p base w
        subst N
        simp_all only [Fin.getElem_fin, h_1_iter_zero, not_lt_zero, not_isEmpty_of_nonempty, IsEmpty.forall_iff,
          implies_true, Rfix, base, I]
      unfold base at hw_eq_I; simp_all +decide [ h_1_base ] 
      grind
    have hw_eq_I : w = I := by
      convert get_unitary_init_is_init p u_i
      constructor <;> intro h
      · convert get_unitary_init_is_init p u_i
      · convert get_unitary_init_is_init p u_i
        constructor <;> intro h <;> simp_all +decide [ Finset.ext_iff, Set.ext_iff ]
        exact h w |>.1 ( by simpa [ Fin.ext_iff ] using hw_eq_I )
    exact hw_eq_I.symm ▸ ⟨ WeightedDiGraph.Walk.nil, by simp +decide [ h1_goal_value_init_zero ] ⟩
  · obtain ⟨a, ha₁, ha₂, ha₃, ha₄⟩ := h_1_rank_attained p base w hw (Nat.pos_of_ne_zero hw0)
    have hvf : (h_1_iter p base (h_1_rank p base w - 1))[h1_argmax_pre p a (hp a ha₁)] = Rfix[h1_argmax_pre p a (hp a ha₁)] := by
      apply withTop_eq_of_getD_eq
      · apply vec_to_state_isSome_of_applicable
        exact ha₂
        exact h1_argmax_pre_mem p a ( hp a ha₁ )
      · apply h_1_iter_fix_isSome_of_iter
        apply vec_to_state_isSome_of_applicable
        exact ha₂
        exact h1_argmax_pre_mem p a ( hp a ha₁ )
      · refine' le_antisymm _ _
        · have h_max_le : ∀ {l : List ℕ}, ∀ x ∈ l, x ≤ List.foldl max 0 l := by
            intro l
            induction' l using List.reverseRecOn with l y ih
            · intro x hx; simp at hx
            · intro x hx
              rw [List.foldl_append]
              simp only [List.foldl_cons, List.foldl_nil]
              rcases List.mem_append.mp hx with h | h
              · exact le_trans (ih x h) (le_max_left _ _)
              · simp only [List.mem_singleton] at h; subst h; exact le_max_right _ _
          convert h_max_le _ _ using 1
          rotate_left
          exact List.map ( fun j => Option.getD ( h_1_iter p base ( h_1_rank p base w - 1 ) )[j] 0 ) a.pre'.val
          · exact List.mem_map.mpr ⟨ _, h1_argmax_pre_mem p a ( hp a ha₁ ), rfl ⟩
          · convert h1_argmax_pre_foldl_max p a ( hp a ha₁ ) |> Eq.symm using 1
            · exact h1_goal_value_eq_fixpoint p _ ( h_1_iter_fix_isSome_of_iter _ _ _ _ ( vec_to_state_isSome_of_applicable _ _ _ ha₂ _ ( h1_argmax_pre_mem _ _ _ ) ) ) ▸ rfl
            · convert ha₄.2 using 2
              refine' List.map_congr_left _
              intro j hj; exact (by
              rw [ h1_goal_value_eq_fixpoint ]
              · rfl
              · exact h_1_iter_fix_isSome_of_iter p base _ _ ( vec_to_state_isSome_of_applicable _ _ _ ha₂ _ hj ))
        · apply withTop_getD_le_getD
          · exact h_1_iter_fix_le_iter p base _ _
          · apply vec_to_state_isSome_of_applicable
            exact ha₂
            exact h1_argmax_pre_mem p a ( hp a ha₁ )
    have hvf_rank : h_1_rank p base (h1_argmax_pre p a (hp a ha₁)) < h_1_rank p base w := by
      convert Nat.lt_of_le_of_lt ( h_1_rank_le p base _ hvf ) ( Nat.pred_lt hw0 ) using 1
    obtain ⟨walk_f, hwalk_f⟩ := ih (h_1_rank p base (h1_argmax_pre p a (hp a ha₁))) (by
    linarith) (h1_argmax_pre p a (hp a ha₁)) (by
    grind +suggestions) rfl
    have h_edge_cost : (justification_graph p (h1_pcf p hp)).Payload (h1_argmax_pre p a (hp a ha₁)) w (by
    exact ⟨ ⟨ a, ha₁ ⟩, rfl, by simpa using ha₃ ⟩) ≤ a.cost := by
      convert justification_graph_payload_le p ( h1_pcf p hp ) ⟨ ⟨ a, ha₁ ⟩, rfl, by simpa using ha₃ ⟩ ⟨ a, ha₁ ⟩ rfl ( by simpa using ha₃ ) using 1
    have h_value_recursion : h1_goal_value p w = a.cost + h1_goal_value p (h1_argmax_pre p a (hp a ha₁)) := by
      have h_value_recursion : h1_goal_value p w = a.cost + (a.pre'.val.map (fun j => (h_1_iter p base (h_1_rank p base w - 1))[j].getD 0)).foldl max 0 := by
        have h_value_recursion : (h_1_iter_fix (n + 2) p base)[w] = some (h1_goal_value p w) := by
          exact h1_goal_value_eq_fixpoint p w hw
        exact Option.some_inj.mp ( h_value_recursion.symm.trans ha₄.1 )
      rw [h_value_recursion, ha₄.right]
      rw [ ← h1_argmax_pre_foldl_max p a (hp a ha₁) ]
      congr! 2
      refine' List.map_congr_left _
      intro j hj
      have h_value_recursion : ((h_1_iter_fix (n + 2) p base)[j]).isSome := by
        apply h_1_iter_fix_isSome_of_iter (k := h_1_rank p base w - 1)
        exact vec_to_state_isSome_of_applicable _ _ _ ha₂ _ hj
      exact congr_arg ( fun x : WithTop ℕ => x.getD 0 ) ( h1_goal_value_eq_fixpoint p j h_value_recursion )
    use walk_f.concat ⟨ ⟨ a, ha₁ ⟩, rfl, by simpa using ha₃ ⟩
    rw [ WeightedDiGraph.Walk.concat_inc_cost_by_edge ]
    exact le_trans ( add_le_add h_edge_cost hwalk_f ) ( by linarith )

/-- **The `h^max`–justification-graph correspondence (equality form).** For a discovered fact `w`,
there is a maximiser justification-graph walk from the initial fact to `w` whose cost equals exactly
`h1_goal_value p w`.  Combines the achievability lower bound `h1_goal_value_walk_lb` with the
upper bound `h1_goal_value_le_of_walk`. -/
lemma h1_goal_value_eq_walk_cost {n : ℕ} (p : STRIPS (n + 2)) (hp : has_preconditions p)
    (u_i : unitary_init p) (w : Fin (n + 2))
    (hw : ((h_1_iter_fix (n + 2) p (h_1_base (n + 2) p.init'))[w]).isSome) :
    ∃ walk : (justification_graph p (h1_pcf p hp)).Walk (get_unitary_init p u_i) w,
      walk.cost = h1_goal_value p w := by
  obtain ⟨walk, hwalk⟩ := h1_goal_value_walk_lb p hp u_i w hw
  refine ⟨walk, le_antisymm hwalk ?_⟩
  have := h1_goal_value_le_of_walk p hp walk
  rwa [h1_goal_value_init_zero p u_i, Nat.zero_add] at this

/-
**First crossing of a walk into a vertex set `S`.** A walk from a vertex outside `S` to a vertex
inside `S` has a first edge `(u, v)` crossing the boundary: `u ∉ S`, `v ∈ S`, and the walk splits as
a prefix `P : a ⤳ u`, the crossing edge, and a suffix `Q : v ⤳ b`, with the costs adding up.
-/
lemma walk_first_crossing {V : Type} [FinEnum V] (G : NatGraph V) (S : V → Prop)
    {a b : V} (W : G.Walk a b) (ha : ¬ S a) (hb : S b) :
    ∃ (u v : V) (adj : G.Adj u v) (P : G.Walk a u) (Q : G.Walk v b),
      ¬ S u ∧ S v ∧ W.cost = P.cost + G.edgeCost adj + Q.cost := by
  by_contra h_contra
  induction' W with a b W ih generalizing S
  · contradiction
  · by_cases hw : S W
    · refine' h_contra ⟨ b, W, _, WeightedDiGraph.Walk.nil, _, _, _ ⟩ <;> norm_num [ hw ]
      all_goals tauto
    · rename_i h₁ h₂ h₃
      obtain ⟨ u, v, adj, P, Q, hu, hv, hcost ⟩ := not_not.mp ( h₃ S hw hb )
      refine' h_contra ⟨ u, v, adj, WeightedDiGraph.Walk.cons h₁ P, Q, _, _, _ ⟩
      · assumption
      · assumption
      · convert congr_arg ( fun x => NatGraph.edgeCost h₁ + x ) hcost using 1 ; ring!
        rw [ WeightedDiGraph.Walk.cost ] ; ring!

/-
**Single-crossing normal form of the optimal maximiser walk.** When the goal `g` is discovered
(`hw`) but not zero-cost reachable from the initial fact `i` (`hz`), there is a maximiser
justification-graph walk realising `h1_goal_value p g` whose cost is entirely concentrated before the
first (and only charged) crossing of the goal-zone boundary: a prefix `W : i ⤳ u` (`u` outside the
goal zone) followed by a single cut edge `(u, v)` (`v` in the goal zone), with
`h1_goal_value p g = W.cost + payload(u, v)`.  This is the geometric heart of the Helmert–Domshlak
property.
-/
lemma h1_optimal_walk_single_crossing {n : ℕ} (p : STRIPS (n + 2)) (hp : has_preconditions p)
    (u_i : unitary_init p) (u_g : unitary_goal p)
    (hw : ((h_1_iter_fix (n + 2) p (h_1_base (n + 2) p.init'))[get_unitary_goal p u_g]).isSome)
    (hz : ¬ zero_cost_reachable (justification_graph p (h1_pcf p hp))
      (get_unitary_init p u_i) (get_unitary_goal p u_g)) :
    ∃ (u v : Fin (n + 2))
      (adj : (justification_graph p (h1_pcf p hp)).Adj u v)
      (W : (justification_graph p (h1_pcf p hp)).Walk (get_unitary_init p u_i) u),
      u ∉ goal_zone (justification_graph p (h1_pcf p hp)) (get_unitary_goal p u_g) ∧
      v ∈ goal_zone (justification_graph p (h1_pcf p hp)) (get_unitary_goal p u_g) ∧
      (u, v) ∈ edges_entering_goal_zone (justification_graph p (h1_pcf p hp))
          (get_unitary_goal p u_g) ∧
      h1_goal_value p (get_unitary_goal p u_g)
        = W.cost + (justification_graph p (h1_pcf p hp)).Payload u v adj := by
  obtain ⟨W0, hW0⟩ := h1_goal_value_eq_walk_cost p hp u_i (get_unitary_goal p u_g) hw
  obtain ⟨ u, v, adj, P, Q, hu, hv, hcost ⟩ := walk_first_crossing ( justification_graph p ( h1_pcf p hp ) ) ( fun x => x ∈ goal_zone ( justification_graph p ( h1_pcf p hp ) ) ( get_unitary_goal p u_g ) ) W0 ( by
    exact fun h => hz <| by simpa using mem_goal_zone_iff ( justification_graph p ( h1_pcf p hp ) ) ( get_unitary_goal p u_g ) ( get_unitary_init p u_i ) |>.1 h; ) ( by
    exact goal_mem_goal_zone _ _ )
  obtain ⟨ T, hT ⟩ := walk_of_zero_cost_reachable ( justification_graph p ( h1_pcf p hp ) ) ( mem_goal_zone_iff _ _ _ |>.1 hv )
  refine' ⟨ u, v, adj, P, hu, hv, mem_edges_entering_goal_zone _ _ _ _ adj, _ ⟩
  · assumption
  · exact hv
  · have := h1_goal_value_le_of_walk p hp ( P.concat adj |> WeightedDiGraph.Walk.append <| T ) ; simp_all +decide [ NatGraph.edgeCost ] 
    linarith [ h1_goal_value_init_zero p u_i ]

/-! ### The Helmert–Domshlak reduction (`h^max → additive landmarks`), in full

This section records the *entire* reduction underlying the dominance result `h^{LM-cut} ≥ h^max`
(Helmert and Domshlak, *Landmarks, Critical Paths and Abstractions: What's the Difference Anyway?*,
ICAPS 2009; the "`h^max` to landmarks" theorem and the proof in §"From `h^max` to landmarks",
p. 5).  The theorem states that, for states with finite `h^max` value, `h^max` can be compiled into
a sum of additive *elementary landmark* heuristics in polynomial time.  The whole development in
this file (culminating in `lmcut_h1_dominates`) is the formal counterpart of that proof; its
per-step heart is `h1_goal_value_step_bound` below.

**The reduction, step by step (paper proof).**

0. *Trivial base.*  If `h^max(I) = 0` there is nothing to prove.
   (Formal counterpart: the zero-cost-reachable base case `h1_goal_value_zero`.)

1. *WLOG normalisation.*  Assume `I ≠ ∅`, `G ≠ ∅`, and every operator has at least one
   precondition (otherwise add a dummy fact `d` to `I`, `G` and all preconditions).
   (Formal counterpart: `unitary_init`, `unitary_goal`, `has_preconditions`.)

2. *Compute the `h^max` fact values.*  Determine `h^max` of every fact.
   (Formal counterpart: the fixpoint `h_1_iter_fix`; the per-fact value is `h1_goal_value`,
   identified with the fixpoint entry by `h1_goal_value_eq_fixpoint`.)

3. *Transformation 1 (singleton conditions).*  Turn the goal set and every operator precondition
   into a singleton, keeping a fact of maximal `h^max` value.  This is a further relaxation that
   leaves `h^max(I)` unchanged because the kept fact dominates.
   (Formal counterpart: the i/g normal form `i_g_normal_form` makes `I`/`G` singletons; the
   precondition singleton is realised by the `h^max`-maximiser precondition-choice function
   `h1_pcf` / `h1_argmax_pre`, which for each operator selects the precondition of maximal
   `h1_goal_value`.)

4. *Transformation 2 (single add effect).*  Split each operator `pre = {p}, add = {a₁,…,a_k}`
   into `k` operators `pre = {p}, add = {a_i}`.  Again `h^max` is unchanged.  (Here the split is
   not materialised as new operators; the justification graph below instead records one arc per
   `(chosen precondition, add effect)` pair, which has the same effect.)

5. *Justification graph `G_Π'`.*  Build the weighted digraph whose vertices are the facts and which
   has an arc `u → v` of weight `w` iff some (transformed) operator has precondition `u`, add effect
   `v` and cost `w`.  Then `h^max` of a fact equals the shortest-path distance from `I` to that fact.
   (Formal counterpart: `justification_graph p (h1_pcf p hp)`; the shortest-path/`h^max`
   correspondence is `h1_goal_value_le_of_walk` (upper bound) and `h1_goal_value_walk_lb`
   (achievability), combined in `h1_goal_value_eq_walk_cost`.)

6. *Cut and three zones.*  Partition the facts into
   * the **goal zone** `V*` — facts from which `g` is reachable at cost `0`
   * the **before-goal zone** `V'` — facts reachable from `I` without ever entering `V*`
   * the **beyond-goal zone** — everything else.
   The chosen cut is the set of all arcs from `V'` into `V*`; let `L` be the operators inducing it.
   (Formal counterpart: `goal_zone`, `edges_entering_goal_zone`, and the landmark
   `(lmcut_step …).1 = landmark_induced_by_cut`.)

7. *`L` is a landmark and yields the partition.*  Removing `L` disconnects `I` from `g`, so `L` is
   an `I`-landmark of `Π'`, hence of `Π⁺`.  Set `h₁` := the elementary landmark heuristic for `L`
   with `cost₁(o) = c_min := min_{o ∈ L} cost(o)` on `L` and `0` elsewhere, and `h₂` := `h^max` with
   `cost₂ := cost − cost₁`.  (Formal counterpart: `lmcut_step` returns `(L, c_min, part)`
   `partition_STRIPS p part 0` is the `cost₁` problem and `partition_STRIPS p part 1` the `cost₂`
   subproblem.  Costs are subtracted on the *relax-equivalence closure* `lm'` of `L`, which is still
   a landmark — `landmark_closure_is_landmark` — keeping the partition valid.)

8. *Condition (a): `c_min > 0`.*  If some `o ∈ L` had cost `0`, there would be a `0`-cost arc from a
   `V'` fact into `V*`, hence a `0`-cost path to `g`, contradicting that the source fact lies in `V'`.
   (Formal counterpart: `lmcut_step_yields_non_zero_heuristic`, with the supporting fact
   `cost_goal_zone_landmark_of_justification_graph`.)  This guarantees `cost₂` has strictly more
   zero-cost operators than `cost`, so the recursion terminates in ≤ `|O|` steps
   (`lmcut_step_subprob_sum_lt`, `lmcut_inner_ge_h1_goal`).

9. *Condition (b): `h₁(I) + h₂(I) ≥ h^max(I)`.*  Here `h₁(I) = c_min` (as `L` is an `I`-landmark),
   so this reduces to `h₂(I) ≥ h^max(I) − c_min`: *reducing the costs of the operators in `L` by
   `c_min` does not reduce `h^max(I)` by more than `c_min`*.  The paper's argument is the
   **single-crossing** observation: every *reasonable* `I → g` path crosses from `V'` to `V*`
   exactly once (after entering `V*`, `g` is reachable for free, so an optimal path never leaves
   `V*` again), so it uses an operator of `L` only once; discounting `L` by `c_min` therefore lowers
   the goal distance by at most `c_min`.  This is exactly `h1_goal_value_step_bound` below.

**Formalisation of condition (b).**  Two ingredients of the single-crossing argument:

* `h1_optimal_walk_single_crossing` — the optimal maximiser walk realising `h^max(g)` is a prefix
  `i ⤳ u` inside `V'` followed by a *single* cut edge `(u,v)` into `V*`, with
  `h^max(g) = W.cost + payload(u,v)`
* `minCost_le_cut_edge_payload` (in `planning.LandmarkCutting`) — every cut edge costs `≥ c_min`
  (the paper's `c_min ≤ cost(o)` for cut operators)
* `h1_lm'_argmax_pre_not_mem_goal_zone` — the maximiser precondition of every reduced (cut-closure)
  operator lies outside `V*` (the geometric reason the discount is only charged once).

The fact that the partition-`1` goal distance drops by at most `c_min` is isolated below into two
sub-lemmas, in terms of which `h1_goal_value_step_bound` is proved:

* `h1_step_postfixpoint_witness` — a *post-fixpoint witness* `w` for the partition-`1` `h^max`
  fixpoint with `w[g] ≥ h^max(g) − c_min` and `w` below the base.  By
  `h_1_iter_fix_ge_of_postfixpoint`, any such witness lower-bounds the partition-`1` fixpoint, which
  is exactly `h₂` evaluated at `g`.  The intended witness is the shortest-path distance in the
  *fixed* `p`-maximiser justification graph re-weighted with partition-`1` payloads (a
  minimum-crossing distance); it is a post-fixpoint because each re-weighted edge satisfies the
  partition-`1` Bellman inequality, and `w[g] ≥ h^max(g) − c_min` because a minimum-crossing
  optimal path spends the `c_min` discount only on its single `V' → V*` crossing.
* `h1_partition_goal_isSome` — the goal fact is *discovered* (finite `h^max`) in the partition-`1`
  subproblem.  Since `partition_STRIPS` preserves preconditions, add-effects and the initial state
  (`partition_STRIPS_getElem_fields`, `partition_STRIPS_init_goal`), the discovered-fact set is
  identical to that of `p`, in which `g` is reachable (`hr`).

The single-crossing post-fixpoint construction rests on `h1_witness_goal_bound`, whose cut-structure
content is discharged by the per-walk single-crossing bound `h1_partition_walk_bound` (built from the
per-edge step `h1_partition_edge_step`). -/

/-
`h1_argmax_pre` depends only on the action's precondition list (and the problem `p`), not on the
rest of the action: two actions of `p` with the same `pre'.val` have the same `h1`-maximiser
precondition.
-/
lemma h1_argmax_pre_congr {m : ℕ} (p : STRIPS m) (a b : Action m)
    (hne_a : a.pre'.val ≠ []) (hne_b : b.pre'.val ≠ [])
    (h : a.pre'.val = b.pre'.val) :
    h1_argmax_pre p a hne_a = h1_argmax_pre p b hne_b := by
  unfold h1_argmax_pre
  grind

/-
**(Geometric crux.)** The `h1`-maximiser precondition of every action in the relax-equivalence
closure of the LM-cut landmark lies *outside* the goal zone of the (maximiser) justification graph.

Reason: an action `l` of the landmark `lmcut_step …` is, by construction, a witness of some cut edge
`(f, t) ∈ edges_entering_goal_zone jg g`, with `f = ↑(h1_pcf p hp l) = h1_argmax_pre p l` and
`t ∈ l.add'`; every edge entering the goal zone has its *source* `f ∉ goal_zone`.  A closure action
`a` shares its preconditions with such an `l` (`delete_relax_action` preserves `pre'`), hence has the
same `h1`-maximiser precondition `f ∉ goal_zone`.
-/
lemma h1_lm'_argmax_pre_not_mem_goal_zone {n : ℕ} (p : STRIPS (n + 2)) (u_g : unitary_goal p)
    (hp : has_preconditions p) (a : Action (n + 2))
    (ha : a ∈ get_all_equiv_delete_relaxed_actions p (lmcut_step p u_g (h1_pcf p hp)).1)
    (hne : a.pre'.val ≠ []) :
    h1_argmax_pre p a hne ∉
      goal_zone (justification_graph p (h1_pcf p hp)) (get_unitary_goal p u_g) := by
  unfold get_all_equiv_delete_relaxed_actions at ha; simp_all +decide [ delete_relax_action ] 
  obtain ⟨ b, hb₁, hb₂, hb₃, hb₄, hb₅ ⟩ := ha.2; simp_all +decide [ h1_pcf ] 
  -- From `hb₁` (membership in `landmark_induced_by_cut`), `b` is a genuine action in `p.actions'`.
  have hb_act : b ∈ p.actions' := by
    unfold lmcut_step at hb₁; simp_all +decide [ landmark_induced_by_cut ] 
    grind +splitIndPred
  -- From `hb₁` (membership in `landmark_induced_by_cut`), there exist a cut edge `(f,t) ∈ edges_entering_goal_zone jg g` and a proof `hl'` with `f = (↑(h1_pcf p hp ⟨b,hl'⟩) : Fin (n+2))` and `t ∈ b.add'.val.toFinset`.
  obtain ⟨ f, t, hf, ht, hft ⟩ : ∃ f t, (f, t) ∈ edges_entering_goal_zone (justification_graph p (h1_pcf p hp)) (get_unitary_goal p u_g) ∧ b.pre'.val ≠ [] ∧ f = h1_argmax_pre p b (hp b hb_act) ∧ t ∈ b.add'.val.toFinset := by
    unfold lmcut_step at hb₁; simp_all +decide [ landmark_induced_by_cut ] 
    unfold h1_pcf at hb₁; simp_all +decide [ h1_argmax_pre ] 
    exact hb₁
  unfold edges_entering_goal_zone at hf; simp_all +decide [ List.mem_flatMap, List.mem_filterMap ] 
  convert hf.2.1 using 1
  rw [ h1_argmax_pre_congr p a b hne ( hp b hb_act ) ( by simpa [ Subtype.ext_iff ] using hb₃ ) ]

/-! ### Discovery (`isSome`) of facts in the maximiser justification graph

In the `h_1`-maximiser justification graph, reachability of a fact from the initial fact implies
that the fact is discovered (`isSome`) at the `h^max` fixpoint.  The key step is that an edge out of
a discovered fact lands in a discovered fact: an edge `f → t` is witnessed by an action `a` whose
*maximiser* precondition is `f`; if `f` is discovered then every precondition of `a` is discovered
(an undiscovered precondition would have the strictly larger `h_1` value `maxFinite + 1`,
contradicting that `f` maximises), so `a` is applicable at the fixpoint state and adds `t`. -/

/-
An **undiscovered** fact has `h_1` value `maxFinite + 1` of the `h^max` fixpoint vector.
-/
lemma h1_goal_value_of_not_isSome {n : ℕ} (p : STRIPS (n + 2)) (f : Fin (n + 2))
    (hf : ¬ ((h_1_iter_fix (n + 2) p (h_1_base (n + 2) p.init'))[f]).isSome) :
    h1_goal_value p f
      = Vector.maxFinite (h_1_iter_fix (n + 2) p (h_1_base (n + 2) p.init')) + 1 := by
  -- By definition of `h1_goal_value`, we know that `h1_goal_value p f` is the value of `h_1` at `f` after replacing the goal with `singletonVarSet f`.
  unfold h1_goal_value
  unfold h_1
  simp +decide [ h_1_iter_fix_replace_goal, vec_to_state_getElem, satisfies'_singleton ]
  unfold replace_goal; simp +decide [ singletonVarSet ] 
  grind

/-
A **discovered** fact has `h_1` value at most `maxFinite` of the `h^max` fixpoint vector.
-/
lemma h1_goal_value_le_maxFinite {n : ℕ} (p : STRIPS (n + 2)) (f : Fin (n + 2))
    (hf : ((h_1_iter_fix (n + 2) p (h_1_base (n + 2) p.init'))[f]).isSome) :
    h1_goal_value p f
      ≤ Vector.maxFinite (h_1_iter_fix (n + 2) p (h_1_base (n + 2) p.init')) := by
  -- Apply the lemma `Vector.le_maxFinite` with the given hypothesis `hf`.
  apply le_trans (by
  grind) (Vector.le_maxFinite (h1_goal_value_eq_fixpoint p f hf))

/-
The unitary initial fact is discovered (`isSome`) at the `h^max` fixpoint.
-/
lemma h1_init_isSome {n : ℕ} (p : STRIPS (n + 2)) (u_i : unitary_init p) :
    ((h_1_iter_fix (n + 2) p (h_1_base (n + 2) p.init'))[get_unitary_init p u_i]).isSome := by
  convert h_1_iter_fix_isSome_of_iter p _ _ _ _ using 1
  exact 0
  convert Option.isSome_iff_ne_none.mpr _
  unfold h_1_iter h_1_base; simp +decide [ h_1_iter_zero ] 
  convert get_unitary_init_is_init p u_i
  constructor <;> intro h <;> simp_all +decide [ Finset.ext_iff, Set.ext_iff ]
  · grind +suggestions
  · convert h ( get_unitary_init p u_i ) |>.2 rfl using 1

/-
**An edge of the maximiser justification graph out of a discovered fact lands in a discovered
fact.**
-/
lemma h1_edge_preserves_isSome {n : ℕ} (p : STRIPS (n + 2)) (hp : has_preconditions p)
    {f t : Fin (n + 2)} (adj : (justification_graph p (h1_pcf p hp)).Adj f t)
    (hf : ((h_1_iter_fix (n + 2) p (h_1_base (n + 2) p.init'))[f]).isSome) :
    ((h_1_iter_fix (n + 2) p (h_1_base (n + 2) p.init'))[t]).isSome := by
  obtain ⟨a, ha⟩ := adj
  have h_preconditions : ∀ q ∈ a.val.pre'.val, ((h_1_iter_fix (n + 2) p (h_1_base (n + 2) p.init'))[q]).isSome := by
    intro q hq
    by_contra hq_not_discovered
    have hq_goal_value : h1_goal_value p q = Vector.maxFinite (h_1_iter_fix (n + 2) p (h_1_base (n + 2) p.init')) + 1 := by
      exact h1_goal_value_of_not_isSome p q hq_not_discovered
    have hf_goal_value : h1_goal_value p f ≤ Vector.maxFinite (h_1_iter_fix (n + 2) p (h_1_base (n + 2) p.init')) := by
      exact h1_goal_value_le_maxFinite p f hf
    have hq_le_hf : h1_goal_value p q ≤ h1_goal_value p f := by
      convert h1_argmax_pre_max p a.val ( hp a.val a.property ) hq using 1
      rw [ha.1]; rfl
    linarith [hq_goal_value, hf_goal_value]
  have h_applicable : applicable' a.val (vec_to_state (n + 2) (h_1_iter_fix (n + 2) p (h_1_base (n + 2) p.init'))) = true := by
    unfold applicable' satisfies'; simp_all +decide [ vec_to_state_getElem ] 
  have := h_1_step_applicable_effects p ( h_1_iter_fix ( n + 2 ) p ( h_1_base ( n + 2 ) p.init' ) ) a.val a.property h_applicable t ( by simpa using ha.2 ) ; simp_all +decide [ h_1_iter_fix_is_fixpoint ] 

/-
**A maximiser justification-graph walk out of a discovered fact ends in a discovered fact.**
-/
lemma h1_walk_preserves_isSome {n : ℕ} (p : STRIPS (n + 2)) (hp : has_preconditions p)
    {f t : Fin (n + 2)} (w : (justification_graph p (h1_pcf p hp)).Walk f t)
    (hf : ((h_1_iter_fix (n + 2) p (h_1_base (n + 2) p.init'))[f]).isSome) :
    ((h_1_iter_fix (n + 2) p (h_1_base (n + 2) p.init'))[t]).isSome := by
  induction' w with f t w ih
  · exact hf
  · exact ‹Option.isSome ( h_1_iter_fix ( n + 2 ) p ( h_1_base ( n + 2 ) p.init' ) )[w] = true → Option.isSome ( h_1_iter_fix ( n + 2 ) p ( h_1_base ( n + 2 ) p.init' ) )[ih] = true› ( h1_edge_preserves_isSome p hp ‹_› hf )

/-- **Sub-statement of condition (b): the goal is discovered in the partition-`1` subproblem.**

The partition-`1` cost partitioning `partition_STRIPS p part 1` only relabels operator costs; it
leaves every operator's preconditions and add-effects, and the initial state, unchanged
(`partition_STRIPS_getElem_fields`, `partition_STRIPS_init_goal`).  The `h^max` fixpoint
`h_1_iter_fix` discovers a fact (`isSome`) iff that fact is delete-relaxation reachable, which
depends only on those preserved data and not on costs.  In `p` the goal fact `g` is reachable
(`hr`), so `g` is discovered in the partition-`1` `h^max` fixpoint as well.

This is the discovery half of the paper's condition (b): it lets us identify the partition-`1`
fixpoint entry at `g` with the finite value `h1_goal_value (partition_STRIPS …) g` via
`h1_goal_value_eq_fixpoint`. -/
lemma h1_partition_goal_isSome {n : ℕ} (p : STRIPS (n + 2)) (u_i : unitary_init p)
    (u_g : unitary_goal p) (hp : has_preconditions p)
    (hr : reachable (justification_graph p (h1_pcf p hp))
      (get_unitary_init p u_i) (get_unitary_goal p u_g)) :
    ((h_1_iter_fix (n + 2)
        (partition_STRIPS p (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩)
        (h_1_base (n + 2)
          (partition_STRIPS p (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩).init'))[
      get_unitary_goal p u_g]).isSome := by
  set part := (lmcut_step p u_g (h1_pcf p hp)).2.2
  set p' := partition_STRIPS p part ⟨(1 : ℕ), by omega⟩ with hp'
  -- The initial state is preserved by cost partitioning.
  have hinit : p'.init' = p.init' := (partition_STRIPS_init_goal p part ⟨1, by omega⟩).1
  rw [hinit]
  -- `g` is discovered in `p`'s fixpoint: it is reachable from the (discovered) initial fact.
  have hg : ((h_1_iter_fix (n + 2) p (h_1_base (n + 2) p.init'))[get_unitary_goal p u_g]).isSome :=
    h1_walk_preserves_isSome p hp (walk_of_reachable _ hr).some (h1_init_isSome p u_i)
  -- The `isSome` pattern is preserved under cost partitioning (same preconditions/add-effects).
  refine h_1_iter_fix_isSome_eq_of_fields p p' ?_ ?_ ?_ (h_1_base (n + 2) p.init')
    (get_unitary_goal p u_g) hg
  · exact (partition_STRIPS_actions_length p part ⟨1, by omega⟩).symm
  · intro i h1 h2
    exact ((partition_STRIPS_getElem_fields p part ⟨1, by omega⟩ i h2 h1).1).symm
  · intro i h1 h2
    exact ((partition_STRIPS_getElem_fields p part ⟨1, by omega⟩ i h2 h1).2.1).symm

/-! ### The justification-graph distance is a post-fixpoint of `h_1_step`

For *any* problem and precondition-choice function, the shortest-walk distance from a fixed source
in the justification graph is a post-fixpoint of the `h^max` step operator `h_1_step`.  This is the
general Bellman fact: each action `a` adding a fact `i` contributes the edge
`pcf a → i` of payload `≤ a.cost`, so the triangle inequality `graphDist_edge_le` bounds the
distance to `i` by (distance to `pcf a`) + `a.cost`.  Combined with `h_1_iter_fix_ge_of_postfixpoint`
this is what lets us *lower-bound* an `h^max` fixpoint by a distance in a (possibly different)
justification graph. -/

lemma graphDist_jg_postfixpoint {n : ℕ} (prob : STRIPS (n + 2))
    (pcf : precondition_choice_function prob) (src : Fin (n + 2)) (i : Fin (n + 2)) :
    graphDist (justification_graph prob pcf) src i
      ≤ (h_1_step (n + 2) prob
          (Vector.ofFn (fun f => graphDist (justification_graph prob pcf) src f)))[i] := by
  convert h_1_step_ge_of_action_bound prob ( Vector.ofFn fun f => graphDist ( justification_graph prob pcf ) src f ) i _ using 1
  · grind
  · intro a ha hi ha'; use ( pcf ⟨ a, ha ⟩ : Fin ( n + 2 ) ) ; simp_all +decide [ vec_to_state_getElem ] 
    refine' ⟨ _, _ ⟩
    · convert ( pcf ⟨ a, ha ⟩ ).property using 1
      ext; simp [Action.pre, convertVarSet]
    · have h_edge : ∃ adj : (justification_graph prob pcf).Adj (pcf ⟨a, ha⟩) i, (justification_graph prob pcf).Payload (pcf ⟨a, ha⟩) i adj ≤ a.cost := by
        exact ⟨ ⟨ ⟨ a, ha ⟩, rfl, by simpa using hi ⟩, justification_graph_payload_le prob pcf _ ⟨ a, ha ⟩ rfl ( by simpa using hi ) ⟩
      obtain ⟨ adj, h_adj ⟩ := h_edge
      convert graphDist_edge_le ( justification_graph prob pcf ) adj |> le_trans <| add_le_add_right ( WithTop.coe_le_coe.mpr h_adj ) _ using 1 ; ring!

/-- The precondition-choice function for the partition-`1` subproblem that **mimics the original
`p`-maximiser choice**: for each action it picks the precondition with the largest `h1_goal_value p`
(computed with `p`'s costs).  This is well typed because cost partitioning preserves every action's
preconditions (`partition_STRIPS` keeps `pre'`).  The justification graph induced by this pcf uses
`p`'s argmax edge *sources* together with the partition-`1` edge *payloads* — exactly the re-weighted
graph whose shortest-path distance is the single-crossing post-fixpoint witness. -/
noncomputable def h1_partition_pcf {n : ℕ} (p : STRIPS (n + 2)) (hp : has_preconditions p)
    (u_g : unitary_goal p) :
    precondition_choice_function
      (partition_STRIPS p (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩) :=
  fun a =>
    ⟨h1_argmax_pre p a.val
        (partition_STRIPS_has_preconditions p _ ⟨1, by omega⟩ hp a.val a.property),
      mem_pre_of_mem_pre'_val a.val
        (h1_argmax_pre_mem p a.val
          (partition_STRIPS_has_preconditions p _ ⟨1, by omega⟩ hp a.val a.property))⟩

/-
**Below-base.**  The partition-`1` re-weighted justification-graph distance from the initial
fact lies below the `h^max` base vector: it is `0` at the (unique) initial fact and `≤ ⊤` elsewhere.
-/
lemma h1_partition_witness_below_base {n : ℕ} (p : STRIPS (n + 2)) (u_i : unitary_init p)
    (u_g : unitary_goal p) (hp : has_preconditions p) (i : Fin (n + 2)) :
    (Vector.ofFn (fun f => graphDist
        (justification_graph (partition_STRIPS p (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩)
          (h1_partition_pcf p hp u_g)) (get_unitary_init p u_i) f))[i]
      ≤ (h_1_base (n + 2)
          (partition_STRIPS p (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩).init')[i] := by
  by_cases hi : (partition_STRIPS p (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩).init'[i] = true
  · simp +decide [ h_1_base, Vector.getElem_ofFn ]
    have h_eq : i = get_unitary_init p u_i := by
      have h_eq : i ∈ p.init := by
        convert hi using 1
      exact Set.ext_iff.mp ( get_unitary_init_is_init p u_i ) i |>.1 h_eq
    rw [ h_eq, graphDist_self ]
    subst h_eq
    simp_all only [Fin.mk_one, Fin.isValue, Fin.getElem_fin, ↓reduceIte, zero_le]
  · unfold h_1_base; simp_all +decide [ Vector.getElem_ofFn ] 
    exact le_top

/-! ### Helper lemmas for the single-crossing lower bound -/

/-
Adding a finite constant commutes with infima in `WithTop ℕ`.
-/
lemma iInf_withTop_add {ι : Type*} (f : ι → WithTop ℕ) (c : ℕ) :
    (⨅ i, f i) + (c : WithTop ℕ) = ⨅ i, (f i + (c : WithTop ℕ)) := by
  refine' le_antisymm _ _
  · exact le_iInf fun i => add_le_add ( iInf_le f i ) le_rfl
  · by_cases h : ∃ i, f i = ⨅ i, f i
    · obtain ⟨ i, hi ⟩ := h; exact le_trans ( ciInf_le ( show BddBelow ( Set.range ( fun i => f i + c ) ) from ⟨ ⊥, Set.forall_mem_range.2 fun i => bot_le ⟩ ) i ) ( by simp +decide [ hi ] ) 
    · contrapose! h
      cases h' : ⨅ i, f i <;> simp_all +decide [ WithTop.add_eq_top ]
      cases isEmpty_or_nonempty ι <;> simp_all +decide [ iInf ]
      · simp_all +decide [ Set.range_eq_empty ]
      · exact h'.symm ▸ ( csInf_mem ( Set.range_nonempty f ) )

/-
A justification-graph edge payload is realised by the cost of some witnessing action.
-/
lemma justification_graph_payload_eq_witness {n : ℕ} (prob : STRIPS n)
    (pcf : precondition_choice_function prob) {f t : Fin n}
    (adj : (justification_graph prob pcf).Adj f t) :
    ∃ a : {b : Action n // b ∈ prob.actions'},
      f = (↑(pcf a) : Fin n) ∧ t ∈ a.val.add'.val.toFinset ∧
      (justification_graph prob pcf).Payload f t adj = a.val.cost := by
  unfold justification_graph at *
  grind +suggestions

/-
The second endpoint of an edge entering the goal zone lies in the goal zone.
-/
lemma snd_mem_goal_zone {V : Type} [FinEnum V] (g : NatGraph V) (goal : V) {u v : V}
    (h : (u, v) ∈ edges_entering_goal_zone g goal) : v ∈ goal_zone g goal := by
  unfold edges_entering_goal_zone at h; simp_all +decide [ List.mem_flatMap, List.mem_filterMap ] 

/-- The cost the partition-`1` cost partitioning assigns to action index `i`: the discounted
`cost - minCost` for cut-closure actions, the original cost otherwise. -/
lemma lmcut_step_partition_one_apply {n : ℕ} (prob : STRIPS n) (u_g : unitary_goal prob)
    (pcf : precondition_choice_function prob) (i : Fin prob.actions'.length) :
    (lmcut_step prob u_g pcf).2.2 ⟨1, by omega⟩ i =
      (if prob.actions'[i] ∈ get_all_equiv_delete_relaxed_actions prob (lmcut_step prob u_g pcf).1
        then prob.actions'[i].cost - (lmcut_step prob u_g pcf).2.1
        else prob.actions'[i].cost) := by
  rfl

/-
**Action correspondence under partition-`1` cost partitioning.** Every action of the
partition-`1` subproblem comes from an action `b` of `p` with the same preconditions and add
effects, whose cost is `b.cost - minCost` if `b` is a cut-closure action and `b.cost` otherwise.
-/
lemma h1_partition_action_correspondence {n : ℕ} (p : STRIPS (n + 2)) (u_g : unitary_goal p)
    (hp : has_preconditions p) {a : Action (n + 2)}
    (ha : a ∈ (partition_STRIPS p (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩).actions') :
    ∃ b : Action (n + 2), b ∈ p.actions' ∧ b.pre' = a.pre' ∧ b.add' = a.add' ∧
      a.cost =
        (if b ∈ get_all_equiv_delete_relaxed_actions p (lmcut_step p u_g (h1_pcf p hp)).1
          then b.cost - (lmcut_step p u_g (h1_pcf p hp)).2.1 else b.cost) := by
  obtain ⟨i, hi, hi'⟩ := List.mem_iff_getElem.mp ha
  have hi2 : i < p.actions'.length := by
    rwa [partition_STRIPS_actions_length] at hi
  refine ⟨p.actions'[i], List.getElem_mem hi2, ?_, ?_, ?_⟩
  · have h := (partition_STRIPS_getElem_fields p
      (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩ i hi hi2).1
    rw [hi'] at h
    exact h.symm
  · have h := (partition_STRIPS_getElem_fields p
      (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩ i hi hi2).2.1
    rw [hi'] at h
    exact h.symm
  · have hcost := partition_STRIPS_getElem_cost p
      (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩ i hi hi2
    rw [hi'] at hcost
    rw [hcost, lmcut_step_partition_one_apply]
    simp only [Fin.getElem_fin]

/-
**A cut-closure action adds a goal-zone fact.** Every action in the relax-equivalence closure
of the LM-cut landmark has an add effect lying in the goal zone (it shares its add effects with a
genuine cut action, whose cut target is a goal-zone fact).
-/
lemma h1_lm'_has_goal_zone_add {n : ℕ} (p : STRIPS (n + 2)) (u_g : unitary_goal p)
    (hp : has_preconditions p) {b : Action (n + 2)}
    (hb : b ∈ get_all_equiv_delete_relaxed_actions p (lmcut_step p u_g (h1_pcf p hp)).1) :
    ∃ t : Fin (n + 2), t ∈ b.add'.val.toFinset ∧
      t ∈ goal_zone (justification_graph p (h1_pcf p hp)) (get_unitary_goal p u_g) := by
  unfold get_all_equiv_delete_relaxed_actions at hb
  unfold lmcut_step at hb; simp_all +decide [ landmark_induced_by_cut ] 
  unfold delete_relax_action at hb; simp_all +decide [ h1_pcf ] 
  grind +suggestions

/-
**Per-edge step of the single-crossing bound.** For each edge `x → y` of the partition-`1`
justification graph, either the `h^max` value propagates as usual (`h^max(y) ≤ h^max(x) + payload`,
the non-discounted case), or — when the edge is discounted by a cut-closure action, which always
also adds a goal-zone fact `t` reachable to the goal for free — the goal value is already bounded:
`h^max(g) ≤ h^max(x) + payload + minCost`.
-/
lemma h1_partition_edge_step {n : ℕ} (p : STRIPS (n + 2)) (u_g : unitary_goal p)
    (hp : has_preconditions p) {x y : Fin (n + 2)}
    (adj1 : (justification_graph
        (partition_STRIPS p (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩)
        (h1_partition_pcf p hp u_g)).Adj x y) :
    (h1_goal_value p y ≤ h1_goal_value p x +
        (justification_graph
          (partition_STRIPS p (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩)
          (h1_partition_pcf p hp u_g)).Payload x y adj1)
    ∨ (h1_goal_value p (get_unitary_goal p u_g) ≤ h1_goal_value p x +
        (justification_graph
          (partition_STRIPS p (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩)
          (h1_partition_pcf p hp u_g)).Payload x y adj1
        + (lmcut_step p u_g (h1_pcf p hp)).2.1) := by
  -- Obtain `a : {b // b ∈ (partition_STRIPS …).actions'}` such that `x = ↑(h1_partition_pcf p hp u_g a)` and `y ∈ a.val.add'.val.toFinset` and `pay1 = a.val.cost`.
  obtain ⟨a, ha⟩ : ∃ a : {b : Action (n + 2) // b ∈ (partition_STRIPS p (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩).actions'},
    x = (h1_partition_pcf p hp u_g a).1 ∧ y ∈ a.val.add'.val.toFinset ∧ (justification_graph (partition_STRIPS p (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩) (h1_partition_pcf p hp u_g)).Payload x y adj1 = a.val.cost := by
      convert justification_graph_payload_eq_witness _ _ adj1 using 1
  simp_all +decide [ h1_partition_pcf ] 
  obtain ⟨b, hb⟩ := h1_partition_action_correspondence p u_g hp a.property
  by_cases hb' : b ∈ get_all_equiv_delete_relaxed_actions p (lmcut_step p u_g (h1_pcf p hp)).1
  · obtain ⟨t, ht⟩ := h1_lm'_has_goal_zone_add p u_g hp hb'
    obtain ⟨adj_xt, h_adj_xt⟩ : ∃ adj_xt : (justification_graph p (h1_pcf p hp)).Adj x t, (justification_graph p (h1_pcf p hp)).Payload x t adj_xt ≤ b.cost := by
      have h_edge : ∃ adj : (justification_graph p (h1_pcf p hp)).Adj x t, (justification_graph p (h1_pcf p hp)).Payload x t adj ≤ b.cost := by
        have h_pre : x = h1_argmax_pre p b (hp b hb.1) := by
          rw [ha.left]
          exact h1_argmax_pre_congr p _ _ _ _ ( by simp_all only [Fin.isValue, Fin.mk_one, mem_toFinset, ↓reduceIte,
            true_and] )
        exact ⟨ ⟨ ⟨ b, hb.1 ⟩, h_pre.symm ▸ rfl, by simpa using ht.1 ⟩, justification_graph_payload_le p ( h1_pcf p hp ) _ ⟨ b, hb.1 ⟩ h_pre.symm ( by simpa using ht.1 ) ⟩
      exact h_edge
    obtain ⟨Tg, hTg⟩ : ∃ Tg : (justification_graph p (h1_pcf p hp)).Walk t (get_unitary_goal p u_g), Tg.cost = 0 := by
      exact walk_of_zero_cost_reachable _ ( mem_goal_zone_iff _ _ _ |>.1 ht.2 )
    have h_walk : h1_goal_value p (get_unitary_goal p u_g) ≤ h1_goal_value p t := by
      have := h1_goal_value_le_of_walk p hp Tg; simp_all +decide [ NatGraph.edgeCost ] 
    have h_walk : h1_goal_value p t ≤ (justification_graph p (h1_pcf p hp)).Payload x t adj_xt + h1_goal_value p x := by
      exact h1_goal_value_edge_bound p hp adj_xt
    grind
  · have h_edge : ∃ adj : (justification_graph p (h1_pcf p hp)).Adj (h1_argmax_pre p b (hp b hb.1)) y, (justification_graph p (h1_pcf p hp)).Payload (h1_argmax_pre p b (hp b hb.1)) y adj ≤ b.cost := by
      exact ⟨ ⟨ ⟨ b, hb.1 ⟩, rfl, by simpa [ hb.2.2.1 ] using ha.2.1 ⟩, justification_graph_payload_le p ( h1_pcf p hp ) _ ⟨ b, hb.1 ⟩ rfl ( by simpa [ hb.2.2.1 ] using ha.2.1 ) ⟩
    obtain ⟨ adj, h_adj ⟩ := h_edge
    have := h1_goal_value_edge_bound p hp adj; simp_all +decide [ h1_argmax_pre_congr ] 
    grind +suggestions

/-
**The single-crossing bound along a whole walk.** For any walk `x ⤳ g` of the partition-`1`
justification graph, `h^max(g) ≤ h^max(x) + (walk cost) + minCost`.  Proved by induction on the
walk: at the first discounted edge `h1_partition_edge_step` already closes the bound to the goal
otherwise the `h^max` value propagates and the induction hypothesis applies.
-/
lemma h1_partition_walk_bound {n : ℕ} (p : STRIPS (n + 2)) (u_g : unitary_goal p)
    (hp : has_preconditions p) {x : Fin (n + 2)}
    (W : (justification_graph
        (partition_STRIPS p (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩)
        (h1_partition_pcf p hp u_g)).Walk x (get_unitary_goal p u_g)) :
    h1_goal_value p (get_unitary_goal p u_g) ≤ h1_goal_value p x + W.cost
      + (lmcut_step p u_g (h1_pcf p hp)).2.1 := by
  have h_walk : ∀ {x y : Fin (n + 2)} (W : (justification_graph
      (partition_STRIPS p (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩)
      (h1_partition_pcf p hp u_g)).Walk x y),
      h1_goal_value p y ≤ h1_goal_value p x + W.cost + (lmcut_step p u_g (h1_pcf p hp)).2.1 ∨
      h1_goal_value p (get_unitary_goal p u_g) ≤ h1_goal_value p x + W.cost + (lmcut_step p u_g (h1_pcf p hp)).2.1 := by
        intro x y W
        induction' W with x y adj1 rest ih
        (
        exact Or.inl ( by simp +decide [ WeightedDiGraph.Walk.cost ] ))
        have := h1_partition_edge_step p u_g hp ih; simp_all +decide [ WeightedDiGraph.Walk.cost, NatGraph.edgeCost ] 
        grind
  (
  grind)

/-- **The single-crossing lower bound (deep cut-structure crux).**

The partition-`1` re-weighted justification-graph distance from the initial fact to the goal is at
least `h^max_p(g) − minCost`.  This is the geometric heart of the Helmert–Domshlak per-step bound:
once an optimal walk first enters the goal zone it reaches the goal for free
(`exists_single_crossing_walk_le` — *an optimal path does not benefit from leaving the goal zone*),
and every discounted (cut-closure-witnessed) edge has its source outside the goal zone
(`h1_lm'_argmax_pre_not_mem_goal_zone`); a cut-closure operator used before the zone can be rerouted
directly into the goal zone (it always adds a goal-zone fact, being relax-equivalent to a genuine
cut operator) without increasing cost, so a minimum-cost walk crosses — and is discounted — only
once, by at most `minCost` (`minCost_le_cut_edge_payload`). -/
lemma h1_witness_goal_bound {n : ℕ} (p : STRIPS (n + 2)) (u_i : unitary_init p)
    (u_g : unitary_goal p) (hp : has_preconditions p)
    (hr : reachable (justification_graph p (h1_pcf p hp))
      (get_unitary_init p u_i) (get_unitary_goal p u_g))
    (hz : ¬ zero_cost_reachable (justification_graph p (h1_pcf p hp))
      (get_unitary_init p u_i) (get_unitary_goal p u_g)) :
    (h1_goal_value p (get_unitary_goal p u_g) : WithTop ℕ)
      ≤ graphDist
          (justification_graph
            (partition_STRIPS p (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩)
            (h1_partition_pcf p hp u_g)) (get_unitary_init p u_i) (get_unitary_goal p u_g)
        + ((lmcut_step p u_g (h1_pcf p hp)).2.1 : WithTop ℕ) := by
  -- Per-walk bound: every partition-`1` walk from the initial fact to the goal has cost at least
  -- `h^max(g) - minCost`, by `h1_partition_walk_bound` (started at the initial fact, whose
  -- `h^max` value is `0`).
  have key : ∀ W : (justification_graph
      (partition_STRIPS p (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩)
      (h1_partition_pcf p hp u_g)).Walk (get_unitary_init p u_i) (get_unitary_goal p u_g),
      (h1_goal_value p (get_unitary_goal p u_g) : WithTop ℕ)
        ≤ (W.cost : WithTop ℕ) + ((lmcut_step p u_g (h1_pcf p hp)).2.1 : WithTop ℕ) := by
    intro W
    have h := h1_partition_walk_bound p u_g hp W
    rw [h1_goal_value_init_zero p u_i] at h
    have h' : h1_goal_value p (get_unitary_goal p u_g)
        ≤ W.cost + (lmcut_step p u_g (h1_pcf p hp)).2.1 := by omega
    exact_mod_cast h'
  -- Conclude by taking the infimum over all walks (the definition of `graphDist`).
  calc (h1_goal_value p (get_unitary_goal p u_g) : WithTop ℕ)
      ≤ ⨅ W : (justification_graph
          (partition_STRIPS p (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩)
          (h1_partition_pcf p hp u_g)).Walk (get_unitary_init p u_i) (get_unitary_goal p u_g),
          ((W.cost : WithTop ℕ) + ((lmcut_step p u_g (h1_pcf p hp)).2.1 : WithTop ℕ)) :=
        le_iInf key
    _ = (⨅ W : (justification_graph
          (partition_STRIPS p (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩)
          (h1_partition_pcf p hp u_g)).Walk (get_unitary_init p u_i) (get_unitary_goal p u_g),
          (W.cost : WithTop ℕ)) + ((lmcut_step p u_g (h1_pcf p hp)).2.1 : WithTop ℕ) := by
        rw [iInf_withTop_add]
    _ = graphDist
          (justification_graph
            (partition_STRIPS p (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩)
            (h1_partition_pcf p hp u_g)) (get_unitary_init p u_i) (get_unitary_goal p u_g)
        + ((lmcut_step p u_g (h1_pcf p hp)).2.1 : WithTop ℕ) := by rw [graphDist]

/-- **Sub-statement of condition (b): a single-crossing post-fixpoint witness.**

Writing `g` for the goal fact, `m := minCost` for the cut value and `p'` for the partition-`1`
subproblem, this asserts the existence of a vector `w` that is a **post-fixpoint** of `p'`'s `h^max`
step, lies **below the base**, and satisfies `h^max_p(g) ≤ w[g] + m`.  The witness is the shortest-walk
distance (`graphDist`) from the initial fact in the justification graph `justification_graph p'
(h1_partition_pcf …)` — i.e. `p`'s argmax edges with partition-`1` payloads.  The post-fixpoint
property is the general Bellman fact `graphDist_jg_postfixpoint`; the below-base property is
`h1_partition_witness_below_base`; the goal bound is the single-crossing crux `h1_witness_goal_bound`.
Via `h_1_iter_fix_ge_of_postfixpoint` this yields `h^max_{p'}(g) ≥ h^max_p(g) − m`, condition (b). -/
lemma h1_step_postfixpoint_witness {n : ℕ} (p : STRIPS (n + 2)) (u_i : unitary_init p)
    (u_g : unitary_goal p) (hp : has_preconditions p)
    (hr : reachable (justification_graph p (h1_pcf p hp))
      (get_unitary_init p u_i) (get_unitary_goal p u_g))
    (hz : ¬ zero_cost_reachable (justification_graph p (h1_pcf p hp))
      (get_unitary_init p u_i) (get_unitary_goal p u_g)) :
    ∃ w : _root_.Vector (WithTop ℕ) (n + 2),
      (∀ i : Fin (n + 2),
        w[i] ≤ (h_1_step (n + 2)
          (partition_STRIPS p (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩) w)[i]) ∧
      (∀ i : Fin (n + 2),
        w[i] ≤ (h_1_base (n + 2)
          (partition_STRIPS p (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩).init')[i]) ∧
      (h1_goal_value p (get_unitary_goal p u_g) : WithTop ℕ)
        ≤ w[get_unitary_goal p u_g] + ((lmcut_step p u_g (h1_pcf p hp)).2.1 : WithTop ℕ) := by
  refine ⟨Vector.ofFn (fun f => graphDist
      (justification_graph (partition_STRIPS p (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩)
        (h1_partition_pcf p hp u_g)) (get_unitary_init p u_i) f), ?_, ?_, ?_⟩
  · intro i
    simpa only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta] using
      graphDist_jg_postfixpoint
        (partition_STRIPS p (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩)
        (h1_partition_pcf p hp u_g) (get_unitary_init p u_i) i
  · intro i
    exact h1_partition_witness_below_base p u_i u_g hp i
  · simpa only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta] using
      h1_witness_goal_bound p u_i u_g hp hr hz

/-- **(K2) Helmert–Domshlak property (condition (b) of the reduction).**  In a recursive step of
LM-cut, the `h_1`/`h^max` value of the goal fact decreases by at most the cut value `c_min` when the
cut-closure operators are made cheaper (i.e. when passing to the partition-`1` subproblem):
`h^max_p(g) ≤ c_min + h^max_{p'}(g)`.

This is the formal counterpart of the paper's condition (b) (Helmert–Domshlak 2009, "From `h^max`
to landmarks", p. 5 right column); see the section docstring above for the full reduction.  The
proof combines the two sub-statements `h1_step_postfixpoint_witness` (the single-crossing
post-fixpoint lower bound) and `h1_partition_goal_isSome` (discovery of the goal in the
partition-`1` subproblem): the post-fixpoint witness lower-bounds the partition-`1` `h^max` fixpoint
via `h_1_iter_fix_ge_of_postfixpoint`, and discovery lets us read that fixpoint entry as the finite
value `h^max_{p'}(g)` through `h1_goal_value_eq_fixpoint`. -/
lemma h1_goal_value_step_bound {n : ℕ} (p : STRIPS (n + 2)) (u_i : unitary_init p)
    (u_g : unitary_goal p) (hp : has_preconditions p)
    (hr : reachable (justification_graph p (h1_pcf p hp))
      (get_unitary_init p u_i) (get_unitary_goal p u_g))
    (hz : ¬ zero_cost_reachable (justification_graph p (h1_pcf p hp))
      (get_unitary_init p u_i) (get_unitary_goal p u_g)) :
    h1_goal_value p (get_unitary_goal p u_g) ≤
      (lmcut_step p u_g (h1_pcf p hp)).2.1
        + h1_goal_value (partition_STRIPS p (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩)
            (get_unitary_goal p u_g) := by
  obtain ⟨w, hpf, hbase, hwg⟩ := h1_step_postfixpoint_witness p u_i u_g hp hr hz
  -- The post-fixpoint witness lies below the partition-`1` `h^max` fixpoint at the goal.
  have hle := h_1_iter_fix_ge_of_postfixpoint
      (partition_STRIPS p (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩)
      (h_1_base (n + 2)
        (partition_STRIPS p (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩).init')
      w hpf hbase (get_unitary_goal p u_g)
  -- The goal is discovered in the partition-`1` subproblem, so that fixpoint entry is the finite
  -- value `h1_goal_value (partition_STRIPS …) g`.
  rw [h1_goal_value_eq_fixpoint
      (partition_STRIPS p (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩)
      (get_unitary_goal p u_g)
      (h1_partition_goal_isSome p u_i u_g hp hr)] at hle
  -- Recast `some _` as the `WithTop` coercion, then do the arithmetic over `WithTop ℕ`.
  have hle' : w[get_unitary_goal p u_g]
      ≤ (h1_goal_value (partition_STRIPS p (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩)
            (get_unitary_goal p u_g) : WithTop ℕ) := hle
  have key : (h1_goal_value p (get_unitary_goal p u_g) : WithTop ℕ)
      ≤ (h1_goal_value (partition_STRIPS p (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩)
            (get_unitary_goal p u_g) : WithTop ℕ)
          + ((lmcut_step p u_g (h1_pcf p hp)).2.1 : WithTop ℕ) :=
    le_trans hwg (by gcongr)
  have key' : h1_goal_value p (get_unitary_goal p u_g)
      ≤ h1_goal_value (partition_STRIPS p (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩)
            (get_unitary_goal p u_g)
        + (lmcut_step p u_g (h1_pcf p hp)).2.1 := by exact_mod_cast key
  exact key'.trans_eq (Nat.add_comm _ _)

/-- **Core domination, by strong induction on the recursion of `lmcut_inner`.** For a solvable
problem `p` in unitary i/g form, the value computed by `lmcut_inner` with the `h_1`-maximiser pcf is
at least the `h_1`/`h^max` value of the goal fact. -/
lemma lmcut_inner_ge_h1_goal {n : ℕ} (M : ℕ) :
    ∀ (p : STRIPS (n + 2)) (u_i : unitary_init p) (u_g : unitary_goal p) (hp : has_preconditions p),
      (p.actions'.map (fun a => a.cost)).sum = M →
      Plan p p.init →
      (lmcut_inner p u_i u_g hp (@h1_pcf n)).2.1 ≥ h1_goal_value p (get_unitary_goal p u_g) := by
  induction M using Nat.strong_induction_on with
  | _ M IH =>
    intro p u_i u_g hp hM plan
    by_cases hr : reachable (justification_graph p (h1_pcf p hp))
        (get_unitary_init p u_i) (get_unitary_goal p u_g)
    · by_cases hz : zero_cost_reachable (justification_graph p (h1_pcf p hp))
          (get_unitary_init p u_i) (get_unitary_goal p u_g)
      · rw [lmcut_inner_value_zero p u_i u_g hp (@h1_pcf n) hr hz,
          h1_goal_value_zero p u_i u_g hp hz]
      · -- recursive step
        rw [lmcut_inner_value_step p u_i u_g hp (@h1_pcf n) hr hz]
        have hpos : 0 < (lmcut_step p u_g (h1_pcf p hp)).2.1 :=
          lmcut_step_yields_non_zero_heuristic p u_i u_g (h1_pcf p hp) hr hz
        have hsub_lt :
            ((partition_STRIPS p (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩).actions'.map
              (fun a => a.cost)).sum < M := by
          rw [← hM]; exact lmcut_step_subprob_sum_lt p u_g (h1_pcf p hp) hpos
        -- the subproblem still has a plan (cost partitioning only relabels costs)
        obtain ⟨subplan, _⟩ :=
          plan_transfer_to_partition p (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩ plan
        have hIH := IH _ hsub_lt
          (partition_STRIPS p (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩)
          u_i u_g (partition_STRIPS_has_preconditions p (lmcut_step p u_g (h1_pcf p hp)).2.2
            ⟨1, by omega⟩ hp) rfl subplan
        -- get_unitary_goal is preserved by cost partitioning, so rewrite `hIH` to match `hK2`
        have hgoal_eq :
            get_unitary_goal (partition_STRIPS p (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩)
              u_g = get_unitary_goal p u_g := rfl
        rw [hgoal_eq] at hIH
        have hK2 := h1_goal_value_step_bound p u_i u_g hp hr hz
        exact le_trans hK2 (Nat.add_le_add_left hIH _)
    · exact ((lmcut_no_plan_of_not_reachable p u_i u_g (h1_pcf p hp) hr).false plan).elim

/-- `h_1_iter_fix` ignores the initial state (it depends only on the actions), so `set_init` does not
change it. -/
lemma h_1_iter_fix_set_init {n : ℕ} (prob : STRIPS n) (s : State' n)
    (bef : _root_.Vector (WithTop ℕ) n) :
    h_1_iter_fix n (set_init prob s) bef = h_1_iter_fix n prob bef := by
  unfold h_1_iter_fix
  simp only [show h_1_step n (set_init prob s) = h_1_step n prob from rfl]
  split
  · rfl
  · exact h_1_iter_fix_set_init prob s _
termination_by bef
decreasing_by exact h_1_step_lex_decreasing prob bef ‹_›

/-- `h_1` depends only on the actions, goal and the explicit state argument, so `set_init` (which
only changes the unused initial-state field) leaves it unchanged. -/
lemma h_1_set_init {n : ℕ} (prob : STRIPS n) (s t : State' n) :
    h_1 (set_init prob s) t = h_1 prob t := by
  unfold h_1
  simp only [h_1_iter_fix_set_init]
  rfl


end Validator
