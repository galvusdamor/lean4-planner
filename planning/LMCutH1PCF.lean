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

namespace STRIPS

open List

-- `singletonVarSet` is defined in `planning.Planning` (the singleton variable set `{f}`).

/-- The `h_1` value of reaching a single fact `f` from the initial state of `p`, i.e. `h_1` of the
problem `p` with its goal replaced by the singleton goal `{f}`. -/
def h1_goal_value {m : ℕ} (p : PlanningTask m) (f : Fin m) : ℕ :=
  h_1 (replace_goal p (singletonVarSet f)) p.init'.toBitVec

/-- The fact of `a`'s preconditions with the largest `h_1` value (taking that fact as the goal).
Requires that `a` has at least one precondition (`hne`). -/
def h1_argmax_pre {m : ℕ} (p : PlanningTask m) (a : Action m) (hne : a.pre.toList ≠ []) : Fin m :=
  (a.pre.toList.argmax (fun f => h1_goal_value p f)).get (by
    rw [Option.isSome_iff_ne_none]
    intro h
    exact hne (List.argmax_eq_none.mp h))

/-- `h1_argmax_pre` is one of `a`'s preconditions. -/
lemma h1_argmax_pre_mem {m : ℕ} (p : PlanningTask m) (a : Action m) (hne : a.pre.toList ≠ []) :
    h1_argmax_pre p a hne ∈ a.pre.toList :=
  List.argmax_mem (Option.get_mem _)

/-- `h1_argmax_pre` maximises the `h_1` value over all of `a`'s preconditions. -/
lemma h1_argmax_pre_max {m : ℕ} (p : PlanningTask m) (a : Action m) (hne : a.pre.toList ≠ [])
    {f : Fin m} (hf : f ∈ a.pre.toList) :
    h1_goal_value p f ≤ h1_goal_value p (h1_argmax_pre p a hne) :=
  List.le_of_mem_argmax hf (Option.get_mem _)

/-- **The `h_1`-maximiser precondition-choice function.**

For every problem `p` (with preconditions) and every action `a`, it chooses the precondition of `a`
with the largest `h_1` value, computed by taking that single precondition fact as the goal. -/
def h1_pcf {n : ℕ} :
    Π p : PlanningTask (n + 2), has_preconditions p → precondition_choice_function p :=
  fun p hp a =>
    ⟨h1_argmax_pre p a.val (hp a.val a.property),
      mem_pre_of_mem_pre_val a.val (h1_argmax_pre_mem p a.val (hp a.val a.property))⟩

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
lemma h1_goal_value_eq_zero_of_satisfies {m : ℕ} (p : PlanningTask m) (f : Fin m)
    (hf : satisfies' (singletonVarSet f) p.init'.toBitVec = true) :
    h1_goal_value p f = 0 := by
  unfold h1_goal_value
  exact h_1_goal_aware p (singletonVarSet f) p.init'.toBitVec hf

/-
The unitary initial fact has `h_1`/`h^max` value `0`.
-/
lemma h1_goal_value_init_zero {m : ℕ} (p : PlanningTask m) (u_i : unitary_init p) :
    h1_goal_value p (get_unitary_init p u_i) = 0 := by
      apply h1_goal_value_eq_zero_of_satisfies
      apply (satisfies'_singleton (get_unitary_init p u_i) p.init'.toBitVec).mpr
      have hmem : get_unitary_init p u_i ∈ p.init' := by
        rw [← VarSet.mem_toList_iff]
        unfold get_unitary_init
        exact List.head_mem _
      rw [VarSet.mem_iff] at hmem
      exact hmem

lemma mem_pre_of_mem_regress_add {m : ℕ} (a : Action m) (t : Fin m) (ht : t ∈ a.add.toList)
    {g' : Fin m}
    (hg' : g' ∈ (varset'_of_state' (regress' a (state'_of_varset' (singletonVarSet t)))).toList) :
    g' ∈ a.pre.toList := by
  contrapose! hg';
  unfold regress' varset'_of_state';
  grind +suggestions

lemma h1_goal_value_bellman_argmax {m : ℕ} (p : PlanningTask m) (a : Action m) (ha : a ∈ p.actions')
    (hne : a.pre.toList ≠ []) (t : Fin m) (ht : t ∈ a.add.toList) :
    h1_goal_value p t ≤ a.cost + h1_goal_value p (h1_argmax_pre p a hne) := by
  have hstep : ∀ g' ∈ (varset'_of_state' (regress' a (state'_of_varset' (singletonVarSet t)))).toList,
      h1_goal_value p g' ≤ h1_goal_value p (h1_argmax_pre p a hne) := by
    intros g' hg'
    exact h1_argmax_pre_max p a hne (mem_pre_of_mem_regress_add a t ht hg')
  have hle : h_1 (replace_goal p (varset'_of_state' (regress' a (state'_of_varset' (singletonVarSet t))))) p.init'.toBitVec
      ≤ h1_goal_value p (h1_argmax_pre p a hne) := by
    by_cases hlen : (varset'_of_state' (regress' a (state'_of_varset' (singletonVarSet t)))).toList.length > 1
    · refine le_trans (h_1_multi_atom p _ _ hlen) ?_
      rw [List.max_le_iff]
      intro b hb
      simp only [List.mem_map] at hb
      obtain ⟨g', hg', rfl⟩ := hb
      exact hstep g' hg'
    · interval_cases hln : List.length (varset'_of_state' (regress' a (state'_of_varset' (singletonVarSet t)))).toList <;> simp_all +decide
      · unfold h_1; simp +decide [*, replace_goal]
        simp_all +decide [List.eq_nil_iff_forall_not_mem]
      · obtain ⟨g', hg'⟩ := List.length_eq_one_iff.mp ‹_›
        have hmem : g' ∈ (varset'_of_state' (regress' a (state'_of_varset' (singletonVarSet t)))).toList := by
          rw [hg']; simp
        have hrg : varset'_of_state' (regress' a (state'_of_varset' (singletonVarSet t)))
            = singletonVarSet g' := by
          apply SetLike.coe_injective
          ext z
          rw [SetLike.mem_coe, SetLike.mem_coe, ← VarSet.mem_toList_iff,
            ← VarSet.mem_toList_iff, hg']
          simp [singletonVarSet]
        rw [hrg]
        exact h1_argmax_pre_max p a hne
          (mem_pre_of_mem_regress_add a t (VarSet.mem_toList_iff.mpr ht) hmem)
  calc h1_goal_value p t
      = h_1 (replace_goal p (singletonVarSet t)) p.init'.toBitVec := rfl
    _ ≤ a.cost + h_1 (replace_goal p (varset'_of_state'
          (regress' a (state'_of_varset' (singletonVarSet t))))) p.init'.toBitVec :=
        h_1_singleton_bellman_add p t p.init'.toBitVec a ha ht
    _ ≤ a.cost + h1_goal_value p (h1_argmax_pre p a hne) := by gcongr

lemma jgraph_zero_cost_edge_witness {n : ℕ} (p : PlanningTask (n + 2)) (hp : has_preconditions p)
    {f t : Fin (n + 2)} (adj : (justification_graph p (h1_pcf p hp)).Adj f t)
    (h0 : (justification_graph p (h1_pcf p hp)).Payload f t adj = 0) :
    ∃ a : {b : Action (n + 2) // b ∈ p.actions'},
      (↑(h1_pcf p hp a) : Fin (n + 2)) = f ∧ t ∈ a.val.add.toList.toFinset ∧ a.val.cost = 0 := by
        unfold justification_graph at h0; simp_all +decide [ h1_pcf ] ;
        rw [ List.min_eq_iff ] at h0;
        simp +zetaDelta at *;
        exact ⟨ _, ⟨ h0.choose_spec.1.1.choose, h0.choose_spec.1.1.choose_spec.symm ⟩, h0.choose_spec.1.2, h0.choose_spec.2 ⟩

lemma h1_goal_value_zero_of_zero_walk {n : ℕ} (p : PlanningTask (n + 2)) (hp : has_preconditions p)
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
      have := h1_goal_value_bellman_argmax p a.val a.property ( hp a.val a.property ) _ ( List.mem_toFinset.mp ha₂ ) ; simp_all [ h1_pcf ]
    unfold WeightedDiGraph.Walk.cost at hcost
    simp_all only [forall_const, Nat.add_eq_zero_iff]

/-
**Per-edge propagation bound.** For an edge `f → t` of the maximiser justification graph, the
`h^max` value of `t` is at most the edge payload plus the `h^max` value of `f`.  The payload is the
minimum cost over actions whose chosen precondition is `f` and whose add effect contains `t`; the
minimiser `a*` has `h1_pcf` choice equal to `f`, so the one-step Bellman bound
`h1_goal_value_bellman_argmax` applied to `a*` yields the claim.
-/
lemma h1_goal_value_edge_bound {n : ℕ} (p : PlanningTask (n + 2)) (hp : has_preconditions p)
    {f t : Fin (n + 2)} (adj : (justification_graph p (h1_pcf p hp)).Adj f t) :
    h1_goal_value p t
      ≤ (justification_graph p (h1_pcf p hp)).Payload f t adj + h1_goal_value p f := by
        -- Let `a` be the minimiser action for the edge `f → t`.
        obtain ⟨ a, ha₁, ha₂, ha₃ ⟩ : ∃ a : {b : Action (n + 2) // b ∈ p.actions'}, (↑(h1_pcf p hp a) : Fin (n + 2)) = f ∧ t ∈ a.val.add.toList.toFinset ∧ (justification_graph p (h1_pcf p hp)).Payload f t adj = a.val.cost := by
          unfold justification_graph; simp +decide [ List.min_eq_iff ] at *;
          obtain ⟨ a, ha ⟩ := adj;
          obtain ⟨b, hb⟩ : ∃ b : {b : Action (n + 2) // b ∈ p.actions'}, (↑(h1_pcf p hp b) : Fin (n + 2)) = f ∧ t ∈ b.val.add.toList.toFinset ∧ ∀ c : {b : Action (n + 2) // b ∈ p.actions'}, (↑(h1_pcf p hp c) : Fin (n + 2)) = f → t ∈ c.val.add.toList.toFinset → b.val.cost ≤ c.val.cost := by
            have h_min : ∃ b ∈ Finset.filter (fun c : {b : Action (n + 2) // b ∈ p.actions'} => (↑(h1_pcf p hp c) : Fin (n + 2)) = f ∧ t ∈ c.val.add.toList.toFinset) (Finset.univ : Finset {b : Action (n + 2) // b ∈ p.actions'}), ∀ c ∈ Finset.filter (fun c : {b : Action (n + 2) // b ∈ p.actions'} => (↑(h1_pcf p hp c) : Fin (n + 2)) = f ∧ t ∈ c.val.add.toList.toFinset) (Finset.univ : Finset {b : Action (n + 2) // b ∈ p.actions'}), b.val.cost ≤ c.val.cost := by
              exact Finset.exists_min_image _ _ ⟨ a, by aesop ⟩;
            exact ⟨ h_min.choose, Finset.mem_filter.mp h_min.choose_spec.1 |>.2.1, Finset.mem_filter.mp h_min.choose_spec.1 |>.2.2, fun c hc₁ hc₂ => h_min.choose_spec.2 c ( Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hc₁, hc₂ ⟩ ) ⟩;
          simp_all +decide [ Finset.ext_iff ];
          grind;
        have := h1_goal_value_bellman_argmax p a.val a.property ( hp a.val a.property ) _ ( List.mem_toFinset.mp ha₂ ) ; simp_all +decide [ h1_pcf ] ;

lemma h1_goal_value_le_of_walk {n : ℕ} (p : PlanningTask (n + 2)) (hp : has_preconditions p)
    {v w : Fin (n + 2)} (walk : (justification_graph p (h1_pcf p hp)).Walk v w) :
    h1_goal_value p w ≤ h1_goal_value p v + walk.cost := by
  induction' walk with v w a h ih
  · exact Nat.le_add_right _ _
  · unfold WeightedDiGraph.Walk.cost
    linarith! [ h1_goal_value_edge_bound p hp ih ]

/-- **(K1)** If the goal fact is reachable using only zero-cost edges of the justification graph,
then the `h_1`/`h^max` value of the goal is `0`. -/
lemma h1_goal_value_zero {n : ℕ} (p : PlanningTask (n + 2)) (u_i : unitary_init p) (u_g : unitary_goal p)
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
lemma h1_goal_value_eq_fixpoint {n : ℕ} (p : PlanningTask (n + 2)) (w : Fin (n + 2))
    (hw : ((h_1_iter_fix (n + 2) p (h_1_base (n + 2) p.init'.toBitVec))[w]).isSome) :
    (h_1_iter_fix (n + 2) p (h_1_base (n + 2) p.init'.toBitVec))[w] = some (h1_goal_value p w) := by
  contrapose! hw
  unfold h1_goal_value at hw; simp_all +decide [ h_1 ]
  convert Option.eq_none_iff_forall_not_mem.mpr _
  intro a ha; simp_all +decide [ h_1_iter_fix_replace_goal ]
  split_ifs at hw <;> simp_all +decide [ replace_goal ]
  · rename_i hex
    obtain ⟨x, hx, hxf⟩ := hex
    have hxw : x = w := by simpa [singletonVarSet, VarSet.ofList] using hx
    subst hxw
    rw [vec_to_state_getElem] at hxf
    simp_all

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
lemma h1_argmax_pre_foldl_max {n : ℕ} (p : PlanningTask n) (a : Action n) (hne : a.pre.toList ≠ []) :
    (a.pre.toList.map (fun j => h1_goal_value p j)).foldl max 0
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
lemma justification_graph_payload_le {n : ℕ} (prob : PlanningTask n)
    (pcf : precondition_choice_function prob) {f t : Fin n}
    (adj : (justification_graph prob pcf).Adj f t)
    (a : {b : Action n // b ∈ prob.actions'}) (hf : (↑(pcf a) : Fin n) = f)
    (ht : t ∈ a.val.add.toList.toFinset) :
    (justification_graph prob pcf).Payload f t adj ≤ a.val.cost := by
      apply List.min_le_of_mem;
      simp +decide [ hf, ht, List.mem_map, List.mem_filter ];
      exact ⟨ a, ⟨ ⟨ a.2, hf.symm ⟩, by simpa using ht ⟩, rfl ⟩

/-- **Predecessor step for the justification-graph lower bound.**  A fact `w` with positive
stabilisation rank at the `h_1` fixpoint has a justification-graph predecessor `f`: `f → w` is an
edge, `f` stabilises strictly earlier, `f` is finite at the fixpoint, and the edge cost plus
`h_1`-value of `f` is at most the `h_1`-value of `w`. -/
lemma h1_walk_pred_step {n : ℕ} (p : PlanningTask (n + 2)) (hp : has_preconditions p)
    (w : Fin (n + 2))
    (hw : ((h_1_iter_fix (n + 2) p (h_1_base (n + 2) p.init'.toBitVec))[w]).isSome)
    (hr : 0 < h_1_rank p (h_1_base (n + 2) p.init'.toBitVec) w) :
    ∃ (f : Fin (n + 2)) (adj : (justification_graph p (h1_pcf p hp)).Adj f w),
      h_1_rank p (h_1_base (n + 2) p.init'.toBitVec) f < h_1_rank p (h_1_base (n + 2) p.init'.toBitVec) w ∧
        ((h_1_iter_fix (n + 2) p (h_1_base (n + 2) p.init'.toBitVec))[f]).isSome ∧
        (justification_graph p (h1_pcf p hp)).edgeCost adj + h1_goal_value p f
          ≤ h1_goal_value p w := by
  set base := h_1_base (n + 2) p.init'.toBitVec with hbase
  obtain ⟨a, ha₁, ha₂, ha₃, ha₄, ha₅⟩ := h_1_rank_attained p base w hw hr
  set fixv := h_1_iter_fix (n + 2) p base with hfixv
  have hmem := h1_argmax_pre_mem p a (hp a ha₁)
  have hpreSome : ∀ j ∈ a.pre.toList, (fixv[j]).isSome :=
    fun j hj => h_1_iter_fix_isSome_of_iter p _ _ _
      (vec_to_state_isSome_of_applicable _ _ _ ha₂ j hj)
  have hKey : (a.pre.toList.map (fun j => (fixv[j]).getD 0)).foldl max 0
      = (fixv[h1_argmax_pre p a (hp a ha₁)]).getD 0 := by
    have h1 : (a.pre.toList.map (fun j => (fixv[j]).getD 0)).foldl max 0
        = (a.pre.toList.map (fun j => h1_goal_value p j)).foldl max 0 := by
      refine congr_arg _ (List.map_congr_left ?_)
      intro j hj
      exact congr_arg (fun x : WithTop ℕ => x.getD 0)
        (h1_goal_value_eq_fixpoint p j (hpreSome j hj))
    rw [h1, h1_argmax_pre_foldl_max p a (hp a ha₁), hfixv, hbase]
    simp [h1_goal_value_eq_fixpoint p _ (hpreSome _ hmem)]
  refine ⟨h1_argmax_pre p a (hp a ha₁),
    ⟨⟨a, ha₁⟩, by simp [h1_pcf], by simpa using ha₃⟩, ?_, ?_, ?_⟩
  · refine lt_of_le_of_lt
      (h_1_rank_le p base (h1_argmax_pre p a (hp a ha₁)) (k := h_1_rank p base w - 1) ?_) (by omega)
    refine withTop_eq_of_getD_eq
      (vec_to_state_isSome_of_applicable _ _ _ ha₂ _ hmem)
      (hpreSome _ hmem)
      (le_antisymm ?_ ?_)
    · calc ((h_1_iter p base (h_1_rank p base w - 1))[h1_argmax_pre p a (hp a ha₁)]).getD 0
          ≤ (a.pre.toList.map
              (fun j => ((h_1_iter p base (h_1_rank p base w - 1))[j]).getD 0)).foldl max 0 :=
            le_foldl_max_of_mem
              (fun j => ((h_1_iter p base (h_1_rank p base w - 1))[j]).getD 0) hmem
        _ = (a.pre.toList.map (fun j => (fixv[j]).getD 0)).foldl max 0 := ha₅
        _ = (fixv[h1_argmax_pre p a (hp a ha₁)]).getD 0 := hKey
    · exact withTop_getD_le_getD (h_1_iter_fix_le_iter _ _ _ _)
        (vec_to_state_isSome_of_applicable _ _ _ ha₂ _ hmem)
  · exact hpreSome _ hmem
  · have h_edge_cost_le :
        (justification_graph p (h1_pcf p hp)).Payload (h1_argmax_pre p a (hp a ha₁)) w
          ⟨⟨a, ha₁⟩, by simp [h1_pcf], by simpa using ha₃⟩ ≤ a.cost := by
      convert justification_graph_payload_le p (h1_pcf p hp) _ ⟨a, ha₁⟩ _ _ using 1
      · unfold h1_pcf; simp [h1_argmax_pre]
      · exact List.mem_toFinset.mpr ha₃
    have hvw : h1_goal_value p w
        = a.cost + (a.pre.toList.map (fun j => (fixv[j]).getD 0)).foldl max 0 := by
      have hh : fixv[w]
          = some (a.cost + (a.pre.toList.map (fun j => (fixv[j]).getD 0)).foldl max 0) := by
        rw [ha₄]; unfold actionContribUB; rw [← ha₅]
      exact Option.some_inj.mp (h1_goal_value_eq_fixpoint p w hw ▸ hh)
    have hvf : h1_goal_value p (h1_argmax_pre p a (hp a ha₁))
        = (fixv[h1_argmax_pre p a (hp a ha₁)]).getD 0 := by
      rw [hfixv, hbase]
      simp [h1_goal_value_eq_fixpoint p _ (hpreSome _ hmem)]
    unfold NatGraph.edgeCost
    rw [hvw, hvf, ← hKey]
    omega

lemma h1_goal_value_walk_lb {n : ℕ} (p : PlanningTask (n + 2)) (hp : has_preconditions p)
    (u_i : unitary_init p) (w : Fin (n + 2))
    (hw : ((h_1_iter_fix (n + 2) p (h_1_base (n + 2) p.init'.toBitVec))[w]).isSome) :
    ∃ walk : (justification_graph p (h1_pcf p hp)).Walk (get_unitary_init p u_i) w,
      walk.cost ≤ h1_goal_value p w := by
        have h_ind : ∀ k (v : Fin (n + 2)), h_1_rank p (h_1_base (n + 2) p.init'.toBitVec) v = k → ((h_1_iter_fix (n + 2) p (h_1_base (n + 2) p.init'.toBitVec))[v]).isSome → ∃ walk : (justification_graph p (h1_pcf p hp)).Walk (get_unitary_init p u_i) v, walk.cost ≤ h1_goal_value p v := by
          intro k v hv hv';
          induction' k using Nat.strong_induction_on with k ih generalizing v;
          by_cases hk : 0 < k;
          · obtain ⟨ f, adj, hf, hf', hf'' ⟩ := h1_walk_pred_step p hp v hv' ( by linarith );
            obtain ⟨ walk, hw ⟩ := ih _ ( by linarith ) _ rfl hf';
            exact ⟨ walk.concat adj, by simpa [ WeightedDiGraph.Walk.concat_inc_cost_by_edge ] using by omega ⟩;
          · have h_base : p.init'.toBitVec[v] = true := by
              have h_base : (h_1_iter p (h_1_base (n + 2) p.init'.toBitVec) 0)[v] = (h_1_iter_fix (n + 2) p (h_1_base (n + 2) p.init'.toBitVec))[v] := by
                rw [ ← h_1_rank_spec p ( h_1_base ( n + 2 ) p.init'.toBitVec ) v ] ; aesop;
              unfold h_1_iter at h_base; simp_all +decide [ h_1_base ] ;
              grind;
            have hv_init : v ∈ p.init := by
              rw [init_eq_varset_toFinset]
              simp only [Finset.mem_coe, List.mem_toFinset]
              exact BitVec.mem_toList.mpr (by simpa using h_base)
            have hv_eq : v = get_unitary_init p u_i := by
              rw [get_unitary_init_is_init p u_i] at hv_init
              simpa using hv_init
            subst hv_eq;
            exact ⟨ WeightedDiGraph.Walk.nil, by simp +decide [ h1_goal_value_init_zero p u_i ] ⟩;
        exact h_ind _ _ rfl hw

lemma h1_goal_value_eq_walk_cost {n : ℕ} (p : PlanningTask (n + 2)) (hp : has_preconditions p)
    (u_i : unitary_init p) (w : Fin (n + 2))
    (hw : ((h_1_iter_fix (n + 2) p (h_1_base (n + 2) p.init'.toBitVec))[w]).isSome) :
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
        induction' W with a b W ih <;> simp_all +decide [ Nat.add_assoc ];
        by_cases hW : S W;
        · use b, ha, W, hW, by assumption, WeightedDiGraph.Walk.nil, ‹WeightedDiGraph.Walk W ih›;
          simp [WeightedDiGraph.Walk.cost];
        · obtain ⟨ u, hu, x, hx, adj, P, Q, h ⟩ := ‹¬S W → _› hW;
          use u, hu, x, hx, adj, WeightedDiGraph.Walk.cons ‹_› P, Q;
          simp only [WeightedDiGraph.Walk.cost, h]
          ring

lemma h1_optimal_walk_single_crossing {n : ℕ} (p : PlanningTask (n + 2)) (hp : has_preconditions p)
    (u_i : unitary_init p) (u_g : unitary_goal p)
    (hw : ((h_1_iter_fix (n + 2) p (h_1_base (n + 2) p.init'.toBitVec))[get_unitary_goal p u_g]).isSome)
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
  · have := h1_goal_value_le_of_walk p hp ( P.concat adj |> WeightedDiGraph.Walk.append <| T ) ; simp_all [ NatGraph.edgeCost ]
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
rest of the action: two actions of `p` with the same `pre.val` have the same `h1`-maximiser
precondition.
-/
lemma h1_argmax_pre_congr {m : ℕ} (p : PlanningTask m) (a b : Action m)
    (hne_a : a.pre.toList ≠ []) (hne_b : b.pre.toList ≠ [])
    (h : a.pre.toList = b.pre.toList) :
    h1_argmax_pre p a hne_a = h1_argmax_pre p b hne_b := by
  unfold h1_argmax_pre
  grind

/-
**(Geometric crux.)** The `h1`-maximiser precondition of every action in the relax-equivalence
closure of the LM-cut landmark lies *outside* the goal zone of the (maximiser) justification graph.

Reason: an action `l` of the landmark `lmcut_step …` is, by construction, a witness of some cut edge
`(f, t) ∈ edges_entering_goal_zone jg g`, with `f = ↑(h1_pcf p hp l) = h1_argmax_pre p l` and
`t ∈ l.add`; every edge entering the goal zone has its *source* `f ∉ goal_zone`.  A closure action
`a` shares its preconditions with such an `l` (`delete_relax_action` preserves `pre`), hence has the
same `h1`-maximiser precondition `f ∉ goal_zone`.
-/
lemma h1_lm'_argmax_pre_not_mem_goal_zone {n : ℕ} (p : PlanningTask (n + 2)) (u_g : unitary_goal p)
    (hp : has_preconditions p) (a : Action (n + 2))
    (ha : a ∈ get_all_equiv_delete_relaxed_actions p (lmcut_step p u_g (h1_pcf p hp)).1)
    (hne : a.pre.toList ≠ []) :
    h1_argmax_pre p a hne ∉
      goal_zone (justification_graph p (h1_pcf p hp)) (get_unitary_goal p u_g) := by
  -- Extract a genuine landmark action `l` that is delete-relaxation-equivalent to `a`.
  obtain ⟨l, hl, h_eq⟩ : ∃ l ∈ (lmcut_step p u_g (h1_pcf p hp)).1,
      delete_relax_action a = delete_relax_action l := by
    contrapose! ha; simp_all +decide [get_all_equiv_delete_relaxed_actions]
  -- `a` and `l` share their preconditions (delete relaxation preserves them).
  have hpre : a.pre.toList = l.pre.toList := by
    have h2 : a.pre = l.pre := by
      have := congrArg Action.pre h_eq; simpa [delete_relax_action] using this
    rw [h2]
  have hne_l : l.pre.toList ≠ [] := hpre ▸ hne
  -- `l` lies in the induced landmark, hence witnesses some cut edge `(f, t)`.
  have hl' : l ∈ landmark_induced_by_cut p
      (edges_entering_goal_zone (justification_graph p (h1_pcf p hp))
        (get_unitary_goal p u_g)) (h1_pcf p hp) := by
    simpa [lmcut_step] using hl
  rw [landmark_induced_by_cut, List.mem_flatMap] at hl'
  obtain ⟨⟨f, t⟩, hft, hl2⟩ := hl'
  rw [List.mem_map] at hl2
  obtain ⟨a0, ha0f, ha0v⟩ := hl2
  rw [List.mem_filter, decide_eq_true_eq] at ha0f
  obtain ⟨-, hf, -⟩ := ha0f
  -- The cut edge's source `f` is the `h_1`-maximiser precondition of `l`, and lies outside
  -- the goal zone.
  have hfl : f = h1_argmax_pre p l hne_l := by
    rw [hf]
    simp only [h1_pcf]
    exact h1_argmax_pre_congr p a0.val l (hp a0.val a0.property) hne_l (by rw [ha0v])
  have hf_notin : f ∉
      goal_zone (justification_graph p (h1_pcf p hp)) (get_unitary_goal p u_g) :=
    edges_entering_goal_zone_source_not_mem _ _ hft
  rw [h1_argmax_pre_congr p a l hne hne_l hpre, ← hfl]
  exact hf_notin

lemma h1_goal_value_of_not_isSome {n : ℕ} (p : PlanningTask (n + 2)) (f : Fin (n + 2))
    (hf : ¬ ((h_1_iter_fix (n + 2) p (h_1_base (n + 2) p.init'.toBitVec))[f]).isSome) :
    h1_goal_value p f
      = Vector.maxFinite (h_1_iter_fix (n + 2) p (h_1_base (n + 2) p.init'.toBitVec)) + 1 := by
  unfold h1_goal_value;
  unfold h_1; simp_all +decide [ h_1_iter_fix_replace_goal ] ;
  unfold replace_goal; simp +decide [ VarSet.ofList ] ;
  grind +suggestions

lemma h1_goal_value_le_maxFinite {n : ℕ} (p : PlanningTask (n + 2)) (f : Fin (n + 2))
    (hf : ((h_1_iter_fix (n + 2) p (h_1_base (n + 2) p.init'.toBitVec))[f]).isSome) :
    h1_goal_value p f
      ≤ Vector.maxFinite (h_1_iter_fix (n + 2) p (h_1_base (n + 2) p.init'.toBitVec)) := by
  -- Apply the lemma `Vector.le_maxFinite` with the given hypothesis `hf`.
  apply le_trans (by
  grind) (Vector.le_maxFinite (h1_goal_value_eq_fixpoint p f hf))

/-
The unitary initial fact is discovered (`isSome`) at the `h^max` fixpoint.
-/
lemma h1_init_isSome {n : ℕ} (p : PlanningTask (n + 2)) (u_i : unitary_init p) :
    ((h_1_iter_fix (n + 2) p (h_1_base (n + 2) p.init'.toBitVec))[get_unitary_init p u_i]).isSome := by
      by_contra h_contra;
      have h_unitary_init_zero : h1_goal_value p (get_unitary_init p u_i) = Vector.maxFinite (h_1_iter_fix (n + 2) p (h_1_base (n + 2) p.init'.toBitVec)) + 1 := by
        convert h1_goal_value_of_not_isSome p ( get_unitary_init p u_i ) _ ; aesop;
      exact absurd h_unitary_init_zero ( by linarith [ h1_goal_value_init_zero p u_i ] )

lemma h1_edge_preserves_isSome {n : ℕ} (p : PlanningTask (n + 2)) (hp : has_preconditions p)
    {f t : Fin (n + 2)} (adj : (justification_graph p (h1_pcf p hp)).Adj f t)
    (hf : ((h_1_iter_fix (n + 2) p (h_1_base (n + 2) p.init'.toBitVec))[f]).isSome) :
    ((h_1_iter_fix (n + 2) p (h_1_base (n + 2) p.init'.toBitVec))[t]).isSome := by
  obtain ⟨a, ha⟩ := adj
  have h_preconditions : ∀ q ∈ a.val.pre.toList, ((h_1_iter_fix (n + 2) p (h_1_base (n + 2) p.init'.toBitVec))[q]).isSome := by
    intro q hq
    by_contra hq_not_discovered
    have hq_goal_value : h1_goal_value p q = Vector.maxFinite (h_1_iter_fix (n + 2) p (h_1_base (n + 2) p.init'.toBitVec)) + 1 := by
      exact h1_goal_value_of_not_isSome p q hq_not_discovered
    have hf_goal_value : h1_goal_value p f ≤ Vector.maxFinite (h_1_iter_fix (n + 2) p (h_1_base (n + 2) p.init'.toBitVec)) := by
      exact h1_goal_value_le_maxFinite p f hf
    have hq_le_hf : h1_goal_value p q ≤ h1_goal_value p f := by
      convert h1_argmax_pre_max p a.val ( hp a.val a.property ) hq using 1
      rw [ha.1]; rfl
    linarith [hq_goal_value, hf_goal_value]
  have h_applicable : applicable' a.val (vec_to_state (n + 2) (h_1_iter_fix (n + 2) p (h_1_base (n + 2) p.init'.toBitVec))) = true := by
    unfold applicable' satisfies'; simp_all [ vec_to_state_getElem ]
  have := h_1_step_applicable_effects p ( h_1_iter_fix ( n + 2 ) p ( h_1_base ( n + 2 ) p.init'.toBitVec ) ) a.val a.property h_applicable t ( by simpa using ha.2 ) ; simp_all [ h_1_iter_fix_is_fixpoint ]

/-
**A maximiser justification-graph walk out of a discovered fact ends in a discovered fact.**
-/
lemma h1_walk_preserves_isSome {n : ℕ} (p : PlanningTask (n + 2)) (hp : has_preconditions p)
    {f t : Fin (n + 2)} (w : (justification_graph p (h1_pcf p hp)).Walk f t)
    (hf : ((h_1_iter_fix (n + 2) p (h_1_base (n + 2) p.init'.toBitVec))[f]).isSome) :
    ((h_1_iter_fix (n + 2) p (h_1_base (n + 2) p.init'.toBitVec))[t]).isSome := by
  induction' w with f t w ih
  · exact hf
  · exact ‹Option.isSome ( h_1_iter_fix ( n + 2 ) p ( h_1_base ( n + 2 ) p.init'.toBitVec ) )[w] = true → Option.isSome ( h_1_iter_fix ( n + 2 ) p ( h_1_base ( n + 2 ) p.init'.toBitVec ) )[ih] = true› ( h1_edge_preserves_isSome p hp ‹_› hf )

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
lemma h1_partition_goal_isSome {n : ℕ} (p : PlanningTask (n + 2)) (u_i : unitary_init p)
    (u_g : unitary_goal p) (hp : has_preconditions p)
    (hr : reachable (justification_graph p (h1_pcf p hp))
      (get_unitary_init p u_i) (get_unitary_goal p u_g)) :
    ((h_1_iter_fix (n + 2)
        (partition_STRIPS p (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩)
        (h_1_base (n + 2)
          (partition_STRIPS p (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩).init'.toBitVec))[
      get_unitary_goal p u_g]).isSome := by
  set part := (lmcut_step p u_g (h1_pcf p hp)).2.2
  set p' := partition_STRIPS p part ⟨(1 : ℕ), by omega⟩ with hp'
  -- The initial state is preserved by cost partitioning.
  have hinit : p'.init'.toBitVec = p.init'.toBitVec :=
    congrArg VarSet.toBitVec (partition_STRIPS_init_goal p part ⟨1, by omega⟩).1
  rw [hinit]
  -- `g` is discovered in `p`'s fixpoint: it is reachable from the (discovered) initial fact.
  have hg : ((h_1_iter_fix (n + 2) p (h_1_base (n + 2) p.init'.toBitVec))[get_unitary_goal p u_g]).isSome :=
    h1_walk_preserves_isSome p hp (walk_of_reachable _ hr).some (h1_init_isSome p u_i)
  -- The `isSome` pattern is preserved under cost partitioning (same preconditions/add-effects).
  refine h_1_iter_fix_isSome_eq_of_fields p p' ?_ ?_ ?_ (h_1_base (n + 2) p.init'.toBitVec)
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

lemma graphDist_jg_postfixpoint {n : ℕ} (prob : PlanningTask (n + 2))
    (pcf : precondition_choice_function prob) (src : Fin (n + 2)) (i : Fin (n + 2)) :
    graphDist (justification_graph prob pcf) src i
      ≤ (h_1_step (n + 2) prob
          (Vector.ofFn (fun f => graphDist (justification_graph prob pcf) src f)))[i] := by
  set jg := justification_graph prob pcf with hjg
  set bef : _root_.Vector (WithTop ℕ) (n + 2) :=
    _root_.Vector.ofFn (fun f => graphDist jg src f) with hbef
  have hget : ∀ f, bef[f] = graphDist jg src f := fun f => by simp [hbef]
  rw [← hget i]
  apply h_1_step_ge_of_action_bound prob bef i
  intro a ha hi happ
  refine ⟨(↑(pcf ⟨a, ha⟩) : Fin (n + 2)), ?_, ?_⟩
  · -- the chosen precondition is indeed a precondition of `a`
    have := (pcf ⟨a, ha⟩).2
    simpa [VarSet.toList] using (Action.mem_pre.mp this)
  · -- triangle inequality along the justification edge `pcf a → i`
    have hadj : jg.Adj (↑(pcf ⟨a, ha⟩) : Fin (n + 2)) i :=
      ⟨⟨a, ha⟩, rfl, by simpa using hi⟩
    have hpay : (jg.edgeCost hadj : WithTop ℕ) ≤ (a.cost : WithTop ℕ) := by
      have := justification_graph_payload_le prob pcf hadj ⟨a, ha⟩ rfl (by simpa using hi)
      exact_mod_cast this
    rw [hget i, hget]
    calc graphDist jg src i
          ≤ graphDist jg src (↑(pcf ⟨a, ha⟩)) + (jg.edgeCost hadj : WithTop ℕ) :=
            graphDist_edge_le jg hadj
      _ ≤ graphDist jg src (↑(pcf ⟨a, ha⟩)) + (a.cost : WithTop ℕ) := by gcongr
      _ = (a.cost : WithTop ℕ) + graphDist jg src (↑(pcf ⟨a, ha⟩)) := by
            rw [add_comm]
noncomputable def h1_partition_pcf {n : ℕ} (p : PlanningTask (n + 2)) (hp : has_preconditions p)
    (u_g : unitary_goal p) :
    precondition_choice_function
      (partition_STRIPS p (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩) :=
  fun a =>
    ⟨h1_argmax_pre p a.val
        (partition_STRIPS_has_preconditions p _ ⟨1, by omega⟩ hp a.val a.property),
      mem_pre_of_mem_pre_val a.val
        (h1_argmax_pre_mem p a.val
          (partition_STRIPS_has_preconditions p _ ⟨1, by omega⟩ hp a.val a.property))⟩

/-
**Below-base.**  The partition-`1` re-weighted justification-graph distance from the initial
fact lies below the `h^max` base vector: it is `0` at the (unique) initial fact and `≤ ⊤` elsewhere.
-/
lemma h1_partition_witness_below_base {n : ℕ} (p : PlanningTask (n + 2)) (u_i : unitary_init p)
    (u_g : unitary_goal p) (hp : has_preconditions p) (i : Fin (n + 2)) :
    (Vector.ofFn (fun f => graphDist
        (justification_graph (partition_STRIPS p (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩)
          (h1_partition_pcf p hp u_g)) (get_unitary_init p u_i) f))[i]
      ≤ (h_1_base (n + 2)
          (partition_STRIPS p (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩).init'.toBitVec)[i] := by
  have hII : (partition_STRIPS p (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩).init'.toBitVec
      = p.init'.toBitVec := congrArg VarSet.toBitVec (partition_STRIPS_init_goal p _ _).1
  simp only [Fin.getElem_fin, Vector.getElem_ofFn, h_1_base, Vector.getElem_map,
    Vector.getElem_finRange, hII]
  by_cases hbit : p.init'.toBitVec[i.val] = true
  · rw [if_pos hbit]
    simp only [Fin.eta]
    have hi_init : i = get_unitary_init p u_i := by
      have hmem : i ∈ p.init := mem_convertState.mpr hbit
      rw [get_unitary_init_is_init p u_i, Set.mem_singleton_iff] at hmem
      exact hmem
    rw [hi_init, graphDist_self]
    rfl
  · rw [if_neg hbit]
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
    · obtain ⟨ i, hi ⟩ := h; exact le_trans ( ciInf_le ( show BddBelow ( Set.range ( fun i => f i + c ) ) from ⟨ ⊥, Set.forall_mem_range.2 fun i => bot_le ⟩ ) i ) ( by simp [ hi ] )
    · contrapose! h
      cases h' : ⨅ i, f i <;> simp_all
      cases isEmpty_or_nonempty ι <;> simp_all [ iInf ]
      · simp_all [ Set.range_eq_empty ]
      · exact h'.symm ▸ ( csInf_mem ( Set.range_nonempty f ) )

/-
A justification-graph edge payload is realised by the cost of some witnessing action.
-/
lemma justification_graph_payload_eq_witness {n : ℕ} (prob : PlanningTask n)
    (pcf : precondition_choice_function prob) {f t : Fin n}
    (adj : (justification_graph prob pcf).Adj f t) :
    ∃ a : {b : Action n // b ∈ prob.actions'},
      f = (↑(pcf a) : Fin n) ∧ t ∈ a.val.add.toList.toFinset ∧
      (justification_graph prob pcf).Payload f t adj = a.val.cost := by
        unfold justification_graph; simp +decide [ List.min_eq_iff ] at *;
        obtain ⟨a, ha⟩ : ∃ a : {b : Action n // b ∈ prob.actions'}, f = (↑(pcf a) : Fin n) ∧ t ∈ a.val.add.toList.toFinset := by
          unfold justification_graph at adj; aesop;
        obtain ⟨a, ha⟩ : ∃ a : {b : Action n // b ∈ prob.actions'}, f = (↑(pcf a) : Fin n) ∧ t ∈ a.val.add.toList.toFinset ∧ ∀ b : {b : Action n // b ∈ prob.actions'}, f = (↑(pcf b) : Fin n) → t ∈ b.val.add.toList.toFinset → a.val.cost ≤ b.val.cost := by
          have h_min : ∃ a ∈ Finset.filter (fun c : {b : Action n // b ∈ prob.actions'} => f = (↑(pcf c) : Fin n) ∧ t ∈ c.val.add.toList.toFinset) (Finset.univ : Finset {b : Action n // b ∈ prob.actions'}), ∀ c ∈ Finset.filter (fun c : {b : Action n // b ∈ prob.actions'} => f = (↑(pcf c) : Fin n) ∧ t ∈ c.val.add.toList.toFinset) (Finset.univ : Finset {b : Action n // b ∈ prob.actions'}), a.val.cost ≤ c.val.cost := by
            exact Finset.exists_min_image _ _ ⟨ a, by aesop ⟩;
          exact ⟨ h_min.choose, Finset.mem_filter.mp h_min.choose_spec.1 |>.2.1, Finset.mem_filter.mp h_min.choose_spec.1 |>.2.2, fun b hb₁ hb₂ => h_min.choose_spec.2 b ( Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hb₁, hb₂ ⟩ ) ⟩;
        use a.val, by
          exact ⟨ a.2, ha.1 ⟩, by
          exact List.mem_toFinset.mp ha.2.1 |> fun h => by simpa using h;, by
          aesop, by
          aesop

lemma snd_mem_goal_zone {V : Type} [FinEnum V] (g : NatGraph V) (goal : V) {u v : V}
    (h : (u, v) ∈ edges_entering_goal_zone g goal) : v ∈ goal_zone g goal := by
  unfold edges_entering_goal_zone at h; simp_all [ List.mem_flatMap, List.mem_filterMap ]

/-- The cost the partition-`1` cost partitioning assigns to action index `i`: the discounted
`cost - minCost` for cut-closure actions, the original cost otherwise. -/
lemma lmcut_step_partition_one_apply {n : ℕ} (prob : PlanningTask n) (u_g : unitary_goal prob)
    (pcf : precondition_choice_function prob) (i : Fin prob.actions'.length) :
    (lmcut_step prob u_g pcf).2.2 ⟨1, by omega⟩ i =
      (if prob.actions'[i] ∈ get_all_equiv_delete_relaxed_actions prob (lmcut_step prob u_g pcf).1
        then prob.actions'[i].cost - (lmcut_step prob u_g pcf).2.1
        else prob.actions'[i].cost) := by
  unfold lmcut_step
  dsimp only

/-
**Action correspondence under partition-`1` cost partitioning.** Every action of the
partition-`1` subproblem comes from an action `b` of `p` with the same preconditions and add
effects, whose cost is `b.cost - minCost` if `b` is a cut-closure action and `b.cost` otherwise.
-/
lemma h1_partition_action_correspondence {n : ℕ} (p : PlanningTask (n + 2)) (u_g : unitary_goal p)
    (hp : has_preconditions p) {a : Action (n + 2)}
    (ha : a ∈ (partition_STRIPS p (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩).actions') :
    ∃ b : Action (n + 2), b ∈ p.actions' ∧ b.pre = a.pre ∧ b.add = a.add ∧
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
lemma h1_lm'_has_goal_zone_add {n : ℕ} (p : PlanningTask (n + 2)) (u_g : unitary_goal p)
    (hp : has_preconditions p) {b : Action (n + 2)}
    (hb : b ∈ get_all_equiv_delete_relaxed_actions p (lmcut_step p u_g (h1_pcf p hp)).1) :
    ∃ t : Fin (n + 2), t ∈ b.add.toList.toFinset ∧
      t ∈ goal_zone (justification_graph p (h1_pcf p hp)) (get_unitary_goal p u_g) := by
  unfold get_all_equiv_delete_relaxed_actions at hb
  unfold lmcut_step at hb; simp_all [ landmark_induced_by_cut ]
  unfold delete_relax_action at hb; simp_all [ h1_pcf ]
  grind +suggestions

/-
**Per-edge step of the single-crossing bound.** For each edge `x → y` of the partition-`1`
justification graph, either the `h^max` value propagates as usual (`h^max(y) ≤ h^max(x) + payload`,
the non-discounted case), or — when the edge is discounted by a cut-closure action, which always
also adds a goal-zone fact `t` reachable to the goal for free — the goal value is already bounded:
`h^max(g) ≤ h^max(x) + payload + minCost`.
-/
lemma h1_partition_edge_step {n : ℕ} (p : PlanningTask (n + 2)) (u_g : unitary_goal p)
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
  obtain ⟨a, hxeq, hyadd, hpay⟩ := justification_graph_payload_eq_witness (partition_STRIPS p (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩) (h1_partition_pcf p hp u_g) adj1;
  obtain ⟨i, hi, ha_eq⟩ := List.mem_iff_getElem.mp a.2
  have hi_lt' : i < p.actions'.length := by
    exact hi.trans_le ( by simp +decide [ partition_STRIPS_actions_length ] )
  set a0 := p.actions'[i] with ha0_def
  have ha0_mem : a0 ∈ p.actions' := by
    exact List.getElem_mem _
  have ha0_pre : a.val.pre.toList = a0.pre.toList := by
    rw [ ← ha_eq ];
    simp +decide [ partition_STRIPS, List.getElem_mapFinIdx ];
    rfl
  have ha0_add : a.val.add.toList = a0.add.toList := by
    rw [ ← ha_eq ];
    unfold partition_STRIPS; aesop;
  have ha0_cost : a.val.cost = (if a0 ∈ get_all_equiv_delete_relaxed_actions p (lmcut_step p u_g (h1_pcf p hp)).1 then a0.cost - (lmcut_step p u_g (h1_pcf p hp)).2.1 else a0.cost) := by
    have h := partition_STRIPS_getElem_cost p (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩ i hi hi_lt'
    rw [← ha_eq, h]
    exact lmcut_step_partition_one_apply p u_g (h1_pcf p hp) ⟨i, hi_lt'⟩
  have ha0_argmax : x = h1_argmax_pre p a0 (hp a0 ha0_mem) := by
    rw [hxeq, h1_partition_pcf];
    convert h1_argmax_pre_congr p a.val a0 _ _ ha0_pre using 1;
  have ha0_bellman : h1_goal_value p y ≤ a0.cost + h1_goal_value p (h1_argmax_pre p a0 (hp a0 ha0_mem)) := by
    apply h1_goal_value_bellman_argmax p a0 ha0_mem (hp a0 ha0_mem) y (by
    simp_all +decide [ Finset.ext_iff ]);
  split_ifs at ha0_cost <;> simp_all +decide [ add_comm ];
  obtain ⟨ t, ht₁, ht₂ ⟩ := h1_lm'_has_goal_zone_add p u_g hp ‹_›;
  have ha0_bellman_t : h1_goal_value p (get_unitary_goal p u_g) ≤ h1_goal_value p t := by
    have := walk_of_zero_cost_reachable ( justification_graph p ( h1_pcf p hp ) ) ( mem_goal_zone_iff ( justification_graph p ( h1_pcf p hp ) ) ( get_unitary_goal p u_g ) t |>.1 ht₂ ) ; simp_all +decide [ h1_goal_value_le_of_walk ] ;
    obtain ⟨ w, hw ⟩ := this; exact h1_goal_value_le_of_walk p hp w |> le_trans <| by simp +decide [ hw ] ;
  have ha0_bellman_t : h1_goal_value p t ≤ a0.cost + h1_goal_value p (h1_argmax_pre p a0 (hp a0 ha0_mem)) := by
    apply h1_goal_value_bellman_argmax p a0 ha0_mem (hp a0 ha0_mem) t (by
    exact List.mem_toFinset.mp ht₁);
  grind

/-
**The single-crossing bound along a whole walk.** For any walk `x ⤳ g` of the partition-`1`
justification graph, `h^max(g) ≤ h^max(x) + (walk cost) + minCost`.  Proved by induction on the
walk: at the first discounted edge `h1_partition_edge_step` already closes the bound to the goal
otherwise the `h^max` value propagates and the induction hypothesis applies.
-/
lemma h1_partition_walk_bound {n : ℕ} (p : PlanningTask (n + 2)) (u_g : unitary_goal p)
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
        exact Or.inl ( by simp [ WeightedDiGraph.Walk.cost ] ))
        have := h1_partition_edge_step p u_g hp ih; simp_all [ WeightedDiGraph.Walk.cost, NatGraph.edgeCost ]
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
lemma h1_witness_goal_bound {n : ℕ} (p : PlanningTask (n + 2)) (u_i : unitary_init p)
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
lemma h1_step_postfixpoint_witness {n : ℕ} (p : PlanningTask (n + 2)) (u_i : unitary_init p)
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
          (partition_STRIPS p (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩).init'.toBitVec)[i]) ∧
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
lemma h1_goal_value_step_bound {n : ℕ} (p : PlanningTask (n + 2)) (u_i : unitary_init p)
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
        (partition_STRIPS p (lmcut_step p u_g (h1_pcf p hp)).2.2 ⟨1, by omega⟩).init'.toBitVec)
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

/-
**Core domination, by strong induction on the recursion of `lmcut_inner`.** For a solvable
problem `p` in unitary i/g form, the value computed by `lmcut_inner` with the `h_1`-maximiser pcf is
at least the `h_1`/`h^max` value of the goal fact.
-/
lemma lmcut_inner_ge_h1_goal {n : ℕ} (M : ℕ) :
    ∀ (p : PlanningTask (n + 2)) (u_i : unitary_init p) (u_g : unitary_goal p) (hp : has_preconditions p),
      (p.actions'.map (fun a => a.cost)).sum = M →
      PlanningTask.Plan p p.init →
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
        simp
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
        exact le_trans ( mod_cast hK2 ) ( add_le_add le_rfl hIH )
    · exact ((lmcut_no_plan_of_not_reachable p u_i u_g (h1_pcf p hp) hr).false plan).elim

/-- `h_1_iter_fix` ignores the initial state (it depends only on the actions), so `set_init` does not
change it. -/
lemma h_1_iter_fix_set_init {n : ℕ} (prob : PlanningTask n) (s : BitVec n)
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
lemma h_1_set_init {n : ℕ} (prob : PlanningTask n) (s t : BitVec n) :
    h_1 (set_init prob s) t = h_1 prob t := by
  unfold h_1
  simp only [h_1_iter_fix_set_init]
  rfl


end STRIPS
