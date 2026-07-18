import Mathlib.Tactic.Linarith

import planning.CriticalPath
import planning.PerfectHeuristic

import planning.temp

namespace STRIPS

/-
If two vectors are componentwise ≤ in WithTop ℕ and differ, then the first is
    lexicographically less than the second under `withTop.lex Nat.lt`.
-/
lemma vector_le_ne_implies_lex {n : ℕ} (v1 v2 : Vector (WithTop ℕ) n)
    (hle : ∀ i : Fin n, v1[i] ≤ v2[i])
    (hne : v1 ≠ v2) :
    Vector.Lex n (withTop.lex Nat.lt) v1 v2 := by
      -- Since $v1 \neq v2$, there must be some $i$ such that $v1[i] \neq v2[i]$.
      obtain ⟨i, hi⟩ : ∃ i : Fin n, v1[i] ≠ v2[i] := by
        contrapose! hne;
        ext i;
        exact hne ⟨ i, by assumption ⟩;
      induction' n with n ih <;> simp_all +decide [ Vector.Lex ];
      · exact Fin.elim0 i;
      · -- Consider two cases: either the first element of v1 is less than the first element of v2, or they are equal and we can apply the induction hypothesis to the rest of the vectors.
        by_cases h_first : v1[0] < v2[0];
        · rcases v1 with ⟨ _ | ⟨ a, v1 ⟩, hv1 ⟩ <;> rcases v2 with ⟨ _ | ⟨ b, v2 ⟩, hv2 ⟩ <;> simp_all +decide [ List.Lex ];
          · cases hv2;
          · cases h : a <;> cases h' : b <;> simp_all +decide [ withTop.lex ];
            · exact List.Lex.rel ( by simp +decide [ withTop.lex ] );
            · exact List.Lex.rel ( by aesop );
        · cases eq_or_lt_of_le ( hle 0 ) <;> simp_all +decide [ List.Lex ];
          · specialize ih ( v1.tail ) ( v2.tail ) ; simp_all +decide [ Fin.forall_fin_succ, List.Lex ];
            specialize ih ( fun i => by simpa only [ add_comm ] using hle i ) ( by
              intro h; simp_all +decide [ Vector.ext_iff ] ;
              induction i using Fin.inductionOn <;> simp_all +decide [ add_comm 1 ] );
            rcases i with ⟨ _ | i, hi ⟩ <;> simp_all +decide [ add_comm ];
            specialize ih ⟨ i, by linarith ⟩ hi;
            rcases v1 with ⟨ _ | ⟨ a, v1 ⟩, hv1 ⟩ <;> rcases v2 with ⟨ _ | ⟨ b, v2 ⟩, hv2 ⟩ <;> simp_all +decide [ List.Lex ];
            simp_all +decide [ List.take_of_length_le ( show v1.length ≤ n from by { have := hv1; simp_all +decide [ Vector.size ] } ) ];
            rw [ List.take_of_length_le ( by simpa [ List.length ] using hv2.le ) ] at ih ; exact List.Lex.cons ih;
          · exact absurd ‹_› ( not_lt_of_ge h_first )

lemma h_1_step_lex_decreasing {n : ℕ} (prob : PlanningTask n) (bef : Vector (WithTop ℕ) n)
    (hne : h_1_step n prob bef ≠ bef) :
    Vector.Lex n (withTop.lex Nat.lt) (h_1_step n prob bef) bef := by
  exact vector_le_ne_implies_lex _ _ (fun i => h_1_step_le n prob bef i) hne

-- termination by the fact that h_1_step is monotone in its bef argument
def h_1_iter_fix (n : ℕ) (prob : PlanningTask n) (bef : Vector (WithTop ℕ) n) : Vector (WithTop ℕ) n :=
  let next := h_1_step n prob bef
  if _forTermination : next = bef then
    bef
  else
    h_1_iter_fix n prob next
termination_by bef
decreasing_by exact h_1_step_lex_decreasing prob bef _forTermination

/-- At the fixpoint, h_1_step is idempotent. -/
lemma h_1_iter_fix_is_fixpoint (n : ℕ) (prob : PlanningTask n) (bef : Vector (WithTop ℕ) n) :
    h_1_step n prob (h_1_iter_fix n prob bef) = h_1_iter_fix n prob bef := by
  rw [h_1_iter_fix]
  split
  · assumption
  · exact h_1_iter_fix_is_fixpoint n prob (h_1_step n prob bef)
termination_by bef
decreasing_by exact h_1_step_lex_decreasing prob bef ‹_›

/-- h_1_iter_fix is componentwise ≤ the input. -/
lemma h_1_iter_fix_le (n : ℕ) (prob : PlanningTask n) (bef : Vector (WithTop ℕ) n) (i : Fin n) :
    (h_1_iter_fix n prob bef)[i] ≤ bef[i] := by
  rw [h_1_iter_fix]
  split
  · exact le_refl _
  · exact le_trans (h_1_iter_fix_le n prob (h_1_step n prob bef) i) (h_1_step_le n prob bef i)
termination_by bef
decreasing_by exact h_1_step_lex_decreasing prob bef ‹_›

/-- Maximum finite value in a WithTop ℕ vector, returning 0 if all entries are ⊤. -/
def Vector.maxFinite {n : ℕ} (v : Vector (WithTop ℕ) n) : ℕ :=
  v.toList.foldl (fun acc x => match x with | some c => max acc c | none => acc) 0

private lemma foldl_max_ge_elem (l : List (WithTop ℕ)) (acc : ℕ) (c : ℕ)
    (hmem : (some c : WithTop ℕ) ∈ l) :
    l.foldl (fun acc x => match x with | some c => max acc c | none => acc) acc ≥ c := by
      induction' l using List.reverseRecOn with l ih;
      · contradiction;
      · grind

/-
Any finite value in the vector is ≤ maxFinite.
-/
lemma Vector.le_maxFinite {n : ℕ} {v : Vector (WithTop ℕ) n} {i : Fin n} {c : ℕ}
    (h : v[i] = some c) : c ≤ Vector.maxFinite v := by
      apply foldl_max_ge_elem;
      simp +decide [ ← h, Fin.cast_val_eq_self ];
      grind


def h_1 {n : ℕ} (prob : PlanningTask n) (s : State' n) : ℕ :=
  let result := h_1_iter_fix n prob (h_1_base n s)
  let s_b := vec_to_state n result

  -- check if the goal has been reached
  if h_sat : satisfies' prob.goal' s_b then
    let pre_cost : List ℕ := prob.goal'.toList.attach.map (fun x : { x : Fin n // x ∈ prob.goal'.toList } =>
      result[x.1].get (by exact vec_to_state_isSome_of_satisfies n result prob.goal' h_sat x.1 (VarSet'.mem_toList.mp x.2)))

    -- cost of the action plus most expensive precondition
    if pre_cost_nil : pre_cost = [] then 0 else pre_cost.max pre_cost_nil
  else
    Vector.maxFinite result + 1 -- dynamic threshold: always ≥ any individual fixpoint value


/-- replace_goal prob g has the same actions as prob. -/
lemma replace_goal_actions' {n : ℕ} (prob : PlanningTask n) (g : VarSet' n) :
    (replace_goal prob g).actions' = prob.actions' := by
  unfold replace_goal; rfl

/-- h_1_step only depends on prob.actions', so replacing the goal doesn't change it. -/
lemma h_1_step_replace_goal {n : ℕ} (prob : PlanningTask n) (g : VarSet' n)
    (bef : Vector (WithTop ℕ) n) :
    h_1_step n (replace_goal prob g) bef = h_1_step n prob bef := by
  unfold h_1_step replace_goal; rfl

/-- The fixpoint result for replace_goal prob g is the same as for prob. -/
lemma h_1_iter_fix_replace_goal {n : ℕ} (prob : PlanningTask n) (g : VarSet' n) (bef : Vector (WithTop ℕ) n) :
    h_1_iter_fix n (replace_goal prob g) bef = h_1_iter_fix n prob bef := by
  unfold h_1_iter_fix
  simp [h_1_step_replace_goal]
  split
  · rfl
  · exact h_1_iter_fix_replace_goal prob g _
termination_by bef
decreasing_by exact h_1_step_lex_decreasing prob bef ‹_›

/-
When s satisfies g, h_1 = 0.
-/
lemma h_1_goal_aware {n : ℕ} (prob : PlanningTask n) (g : VarSet' n) (s : State' n)
    (hsat : satisfies' g s = true) :
    h_1 (replace_goal prob g) s = 0 := by
      revert hsat;
      -- By definition of `h_1_base`, if `s` satisfies `g`, then `h_1_base n s` is a vector where each element is `some 0` if the corresponding variable is true in `s`, and `none` otherwise.
      have h_h1_base : ∀ i : Fin n, (h_1_base n s)[i] = if s[i.val] then some 0 else none := by
        unfold h_1_base; aesop;
      intro hsat
      have h_h1_iter_fix : ∀ i : Fin n, (h_1_iter_fix n (replace_goal prob g) (h_1_base n s))[i] ≤ (h_1_base n s)[i] := by
        exact fun i => h_1_iter_fix_le n ( replace_goal prob g ) ( h_1_base n s ) i;
      unfold h_1; simp_all +decide [ satisfies' ] ;
      split_ifs <;> simp_all +decide [ replace_goal ];
      · have h_h1_iter_fix_zero : ∀ i : Fin n, i ∈ g.val → (h_1_iter_fix n (replace_goal prob g) (h_1_base n s))[i] = some 0 := by
          intro i hi; specialize h_h1_iter_fix i; simp_all +decide [ replace_goal ] ;
          cases h : ( h_1_iter_fix n { varNames := prob.varNames, actions' := prob.actions', init' := prob.init', goal' := g } ( h_1_base n s ) )[ i ] <;> simp_all +decide [ WithTop.some_eq_coe ];
        simp_all +decide [ replace_goal ];
      · obtain ⟨ i, hi, hi' ⟩ := ‹_›; specialize h_h1_iter_fix i; simp_all +decide [ vec_to_state_getElem ] ;

/-
If satisfies' g state holds and i ∈ g, then state[i] = true.
-/
lemma satisfies'_mem {n : ℕ} (g : VarSet' n) (state : State' n) (i : Fin n)
    (hsat : satisfies' g state = true) (hmem : i ∈ g.toList) :
    state[i.val] = true := by
  contrapose! hsat; simp_all [ satisfies', List.all_eq_true ] ;
  use i

/-
satisfies' for a singleton [g_atom] is equivalent to state[g_atom] = true.
-/
lemma satisfies'_singleton {n : ℕ} (g_atom : Fin n) (state : State' n) :
    satisfies' (singletonVarSet g_atom) state = true ↔ state[g_atom.val] = true := by
  unfold satisfies' singletonVarSet; simp +decide [ List.all_eq_true ] ;

/-
If i ∈ g and satisfies' g state, then satisfies' [i] state.
-/
lemma satisfies'_singleton_of_mem {n : ℕ} (g : VarSet' n) (state : State' n) (i : Fin n)
    (hsat : satisfies' g state = true) (hmem : i ∈ g.toList) :
    satisfies' (singletonVarSet i) state = true := by
  -- Since i is in g, and g is satisfied by the state, then the singleton goal for i must be satisfied by the state. This follows directly from the definition of satisfies'.
  apply (satisfies'_singleton i state).mpr (satisfies'_mem g state i hsat hmem)

/-
If ¬ satisfies' g state, then there exists i ∈ g with state[i] = false.
-/
lemma not_satisfies'_exists {n : ℕ} (g : VarSet' n) (state : State' n)
    (hsat : ¬ satisfies' g state = true) :
    ∃ i ∈ g.toList, state[i.val] = false := by
  contrapose! hsat; simp_all [ satisfies', List.all_eq_true ] ;

/-- The result vector for h_1 is the same regardless of the goal. -/
lemma h_1_result_eq {n : ℕ} (prob : PlanningTask n) (g : VarSet' n) (s : State' n) :
    h_1_iter_fix n (replace_goal prob g) (h_1_base n s) = h_1_iter_fix n prob (h_1_base n s) :=
  h_1_iter_fix_replace_goal prob g (h_1_base n s)

/-
h_1_step at position i is bounded by any applicable action's cost contribution.
    This does NOT need the fixpoint assumption.
-/
lemma h_1_step_le_action_contribution {n : ℕ} (prob : PlanningTask n)
    (bef : Vector (WithTop ℕ) n)
    (a : Action n) (ha : a ∈ prob.actions')
    (i : Fin n) (hadd : i ∈ a.add'.toList)
    (happ : applicable' a (vec_to_state n bef) = true) :
    (h_1_step n prob bef)[i] ≤ some (
      if h : a.pre'.toList.attach.map (fun x : { x : Fin n // x ∈ a.pre'.toList } =>
        bef[x.1].get (vec_to_state_isSome_of_applicable n bef a happ x.1 x.2)) = []
      then a.cost
      else a.cost + (a.pre'.toList.attach.map (fun x =>
        bef[x.1].get (vec_to_state_isSome_of_applicable n bef a happ x.1 x.2))).max h) := by
  convert updateIfCheaper_le_newCost _ _ |> le_trans <| WithTop.coe_le_coe.mpr <| List.min_le_of_mem _;
  rw [ h_1_step_getElem ];
  convert if_neg _;
  congr! 1;
  · grind +splitIndPred;
  · grind

/-- At the fixpoint, result[i] ≤ any applicable action's cost contribution. -/
lemma fixpoint_value_le_action_cost {n : ℕ} (prob : PlanningTask n)
    (result : Vector (WithTop ℕ) n)
    (hfix : h_1_step n prob result = result)
    (a : Action n) (ha : a ∈ prob.actions')
    (i : Fin n) (hadd : i ∈ a.add'.toList)
    (happ : applicable' a (vec_to_state n result) = true) :
    result[i] ≤ some (
      if h : a.pre'.toList.attach.map (fun x : { x : Fin n // x ∈ a.pre'.toList } =>
        result[x.1].get (vec_to_state_isSome_of_applicable n result a happ x.1 x.2)) = []
      then a.cost
      else a.cost + (a.pre'.toList.attach.map (fun x =>
        result[x.1].get (vec_to_state_isSome_of_applicable n result a happ x.1 x.2))).max h) := by
  have := h_1_step_le_action_contribution prob result a ha i hadd happ
  rwa [show (h_1_step n prob result)[i] = result[i] from congr_arg (·[i]) hfix] at this

/-
At the fixpoint, if a is applicable and i ∈ a.add, then result[i].get ≤ action cost + max precondition costs.
    Uses List.foldl to compute the max precondition cost to avoid non-emptiness proofs.
-/
lemma fixpoint_get_le_action_cost {n : ℕ} (prob : PlanningTask n)
    (result : Vector (WithTop ℕ) n)
    (hfix : h_1_step n prob result = result)
    (a : Action n) (ha : a ∈ prob.actions')
    (i : Fin n) (hadd : i ∈ a.add'.toList)
    (happ : applicable' a (vec_to_state n result) = true)
    (hi : (result[i]).isSome) :
    (result[i]).get hi ≤
      a.cost + a.pre'.toList.attach.foldl (fun acc (x : { x : Fin n // x ∈ a.pre'.toList }) =>
        max acc ((result[x.1]).get (vec_to_state_isSome_of_applicable n result a happ x.1 x.2))) 0 := by
  have h_le : (result[i]).get hi ≤ (if h : a.pre'.toList.attach.map (fun x : { x : Fin n // x ∈ a.pre'.toList } =>
      result[x.1].get (vec_to_state_isSome_of_applicable n result a happ x.1 x.2)) = []
    then a.cost
    else a.cost + (a.pre'.toList.attach.map (fun x =>
      result[x.1].get (vec_to_state_isSome_of_applicable n result a happ x.1 x.2))).max h) := by
        have := fixpoint_value_le_action_cost prob result hfix a ha i hadd happ; simp_all +decide [ WithTop.le_def ] ;
        obtain ⟨ a, b, hab, h₁, h₂ ⟩ := this; simp_all +decide [ WithTop.some_eq_coe ] ;
        exact hab
  generalize_proofs at *;
  convert h_le using 1;
  cases h : a.pre'.toList.attach <;> simp_all +decide [ List.max ];
  rw [ List.foldl_map ]

/-- Upper-bound contribution of an action `a` at a value vector `v`, using `getD 0` so that no
applicability/`isSome` proof is needed.  When `a` is applicable in `vec_to_state n v` (so every
precondition value `isSome`), `(v[j]).getD 0 = (v[j]).get _`, so this matches the `attach`/`get`
form used by `fixpoint_get_le_action_cost`. -/
def actionContribUB {n : ℕ} (v : Vector (WithTop ℕ) n) (a : Action n) : ℕ :=
  a.cost + (a.pre'.toList.map (fun j => (v[j]).getD 0)).foldl max 0

/-
When `a` is applicable in `vec_to_state n v`, `actionContribUB` (the `getD`-based form) coincides
with the `attach`/`get`-based contribution used inside `h_1_step` and `fixpoint_get_le_action_cost`,
because every precondition value is then `isSome` (so `getD 0 = get`).
-/
lemma actionContribUB_eq_of_applicable {n : ℕ} (v : Vector (WithTop ℕ) n) (a : Action n)
    (happ : applicable' a (vec_to_state n v) = true) :
    actionContribUB v a =
      a.cost + a.pre'.toList.attach.foldl (fun acc (x : { x : Fin n // x ∈ a.pre'.toList }) =>
        max acc ((v[x.1]).get (vec_to_state_isSome_of_applicable n v a happ x.1 x.2))) 0 := by
  simp [ actionContribUB, List.foldl_map ];
  rw [ ← List.foldl_map ];
  convert rfl using 2;
  rw [ ← List.foldl_map ] ; congr! 2;
  refine' List.ext_get _ _ <;> simp ;
  grind +suggestions
/-- For a nonempty list of naturals, `List.max` equals `List.foldl max 0`. -/
lemma list_max_eq_foldl_max_zero (l : List ℕ) (h : l ≠ []) :
    l.max h = l.foldl max 0 := by
  cases l with
  | nil => exact absurd rfl h
  | cons a as =>
    show List.foldl max a as = List.foldl max (max 0 a) as
    rw [Nat.zero_max]

/-
`actionContribUB`-based restatement of `h_1_step_getElem`: the per-index value of `h_1_step`,
with the inline precondition-max replaced by `actionContribUB` (valid since the action is applicable
in the relevant branch).  This removes the dependent precondition proofs, leaving a plain
`filterMap`/`min`/`updateIfCheaper` term.
-/
lemma h_1_step_getElem_contrib {n : ℕ} (prob : PlanningTask n) (v : Vector (WithTop ℕ) n) (i : Fin n) :
    (h_1_step n prob v)[i] =
      (let L : List ℕ := prob.actions'.filterMap (fun a =>
        if i ∈ a.add'.toList then
          if applicable' a (vec_to_state n v) then .some (actionContribUB v a) else .none
        else .none);
      if hL : L = [] then v[i] else updateIfCheaper (L.min hL) v[i]) := by
  rw [h_1_step_getElem];
  simp +decide [ List.filterMap, actionContribUB_eq_of_applicable ];
  congr! 2;
  congr! 2;
  · ext a; split_ifs <;> simp_all +decide [ actionContribUB_eq_of_applicable ] ;
    · grind +splitIndPred;
    · rw [ list_max_eq_foldl_max_zero ];
      rw [ List.foldl_map ];
  · grind

/-
If `h_1_step` strictly changes the value at `i`, the new value is exactly some applicable
adding-action's `actionContribUB` (the action that attained the minimum).
-/
lemma h_1_step_attained {n : ℕ} (prob : PlanningTask n) (v : Vector (WithTop ℕ) n) (i : Fin n)
    (h_ne : (h_1_step n prob v)[i] ≠ v[i]) :
    ∃ a ∈ prob.actions', applicable' a (vec_to_state n v) = true ∧ i ∈ a.add'.toList ∧
      (h_1_step n prob v)[i] = some (actionContribUB v a) := by
  -- Since $h ne$, we know that the $i$-th element of the $h_1_step$ result is exactly some value, and we need to find the corresponding action.
  obtain ⟨a, ha⟩ : ∃ a ∈ prob.actions', applicable' a (vec_to_state n v) = true ∧ i ∈ a.add'.toList ∧ (h_1_step n prob v)[i] = some (actionContribUB v a) := by
    have hL_nonempty : (prob.actions'.filterMap (fun a => if i ∈ a.add'.toList then if applicable' a (vec_to_state n v) then some (actionContribUB v a) else none else none)) ≠ [] := by
      contrapose! h_ne;
      rw [ h_1_step_getElem_contrib, h_ne ] ; simp
    rw [ h_1_step_getElem_contrib ] at *;
    have h_min_mem : (List.min (List.filterMap (fun a => if i ∈ a.add'.toList then if applicable' a (vec_to_state n v) then some (actionContribUB v a) else none else none) prob.actions') hL_nonempty) ∈ List.filterMap (fun a => if i ∈ a.add'.toList then if applicable' a (vec_to_state n v) then some (actionContribUB v a) else none else none) prob.actions' := by
      exact List.min_mem hL_nonempty;
    grind +suggestions;
  use a

/-- Iteration invariant for fixpoint attainment: every discovered fact is either already true in `s`
(value `0` from the base) or has its value bounded **below** by some currently-applicable action that
adds it.  Together with `fixpoint_get_le_action_cost` (the matching upper bound) this pins the value
to an action contribution at the fixpoint. -/
def h1_attained_invariant {n : ℕ} (prob : PlanningTask n) (s : State' n)
    (v : Vector (WithTop ℕ) n) : Prop :=
  ∀ i : Fin n, (v[i]).isSome → s[i] = true ∨
    ∃ a ∈ prob.actions', applicable' a (vec_to_state n v) = true ∧ i ∈ a.add'.toList ∧
      (v[i]).getD 0 ≥ actionContribUB v a

/-
The base vector satisfies the attainment invariant: it is `some 0` exactly at the facts true in
`s`, and `none` elsewhere, so `isSome` forces the `s[i] = true` disjunct.
-/
lemma h1_attained_invariant_base {n : ℕ} (prob : PlanningTask n) (s : State' n) :
    h1_attained_invariant prob s (h_1_base n s) := by
  intro i hi; by_cases hi' : s[i.val] = true <;> simp_all [ h_1_base ] ;

/-
`h_1_step` preserves the attainment invariant.  Values only decrease (`h_1_step_le`) and
applicability only grows (`h_1_step_preserves_isSome`), so an action witnessing the invariant at `v`
still witnesses it (with a no-larger contribution) at `h_1_step n prob v`; an entry whose value
strictly dropped was set to the minimum action contribution, witnessed by the minimiser action.
-/
set_option maxHeartbeats 1000000 in
lemma h1_attained_invariant_step {n : ℕ} (prob : PlanningTask n) (s : State' n)
    (v : Vector (WithTop ℕ) n) (hv : h1_attained_invariant prob s v) :
    h1_attained_invariant prob s (h_1_step n prob v) := by
  intro i hi;
  by_cases h_ne : (h_1_step n prob v)[i] ≠ v[i];
  · obtain ⟨a, ha⟩ := h_1_step_attained prob v i h_ne;
    refine' Or.inr ⟨ a, ha.1, _, ha.2.2.1, _ ⟩ <;> simp_all +decide [ actionContribUB ];
    · unfold applicable' at *; simp_all +decide [ List.all_eq_true ] ;
      intro j hj; specialize ha; have := ha.2.1 j hj; simp_all +decide [ vec_to_state_getElem ] ;
      exact h_1_step_preserves_isSome prob v j ( ha.2.1 j hj );
    · have h_foldl_le : ∀ j : Fin n, (h_1_step n prob v)[j] ≤ v[j] := by
        exact fun j => h_1_step_le n prob v j;
      have h_foldl_le : ∀ {l : List (Fin n)}, (∀ j ∈ l, Option.getD (h_1_step n prob v)[j] 0 ≤ Option.getD v[j] 0) → List.foldl max 0 (List.map (fun j => Option.getD (h_1_step n prob v)[j] 0) l) ≤ List.foldl max 0 (List.map (fun j => Option.getD v[j] 0) l) := by
        intros l hl; induction' l using List.reverseRecOn with l ih <;> simp_all +decide [ List.foldl ] ;
        induction' l using List.reverseRecOn with l ih <;> simp_all +decide [ List.foldl ];
        grind;
      convert h_foldl_le _ using 1;
      intro j hj; specialize ‹∀ j : Fin n, ( h_1_step n prob v )[ j ] ≤ v[ j ] › j; cases h : ( h_1_step n prob v )[ j ] <;> cases h' : v[ j ] <;> simp_all +decide [ WithTop.some_eq_coe ] ;
      · have := vec_to_state_isSome_of_applicable n v a ha.2.1 j ( by simpa using hj ) ; simp_all +decide [ vec_to_state_getElem ] ;
      · exact h_foldl_le;
  · cases h : v[i] <;> simp_all +decide [ Option.isSome_iff_exists ];
    cases hv i ( by aesop ) <;> simp_all +decide [ Option.getD ];
    obtain ⟨ a, ha₁, ha₂, ha₃, ha₄ ⟩ := ‹_›; use Or.inr ⟨ a, ha₁, ?_, ha₃, ?_ ⟩ <;> simp_all +decide [ actionContribUB ] ;
    · grind +suggestions;
    · refine' le_trans _ ha₄;
      have h_foldl_le : ∀ j ∈ a.pre'.toList, (h_1_step n prob v)[j.val] ≤ v[j.val] := by
        exact fun j hj => h_1_step_le n prob v j;
      have h_foldl_le : ∀ j ∈ a.pre'.toList, Option.getD (h_1_step n prob v)[j.val] 0 ≤ Option.getD v[j.val] 0 := by
        intro j hj; specialize h_foldl_le j hj; cases h : ( h_1_step n prob v)[j.val] <;> cases h' : v[j.val] <;> simp_all +decide [ WithTop.some_eq_coe ] ;
        · have := vec_to_state_isSome_of_applicable n v a ha₂ j hj; simp_all +decide [ vec_to_state_getElem ] ;
        · exact h_foldl_le;
      have h_foldl_le : ∀ {l : List (Fin n)}, (∀ j ∈ l, Option.getD (h_1_step n prob v)[j.val] 0 ≤ Option.getD v[j.val] 0) → List.foldl max 0 (List.map (fun j => Option.getD (h_1_step n prob v)[j.val] 0) l) ≤ List.foldl max 0 (List.map (fun j => Option.getD v[j.val] 0) l) := by
        intros l hl; induction' l using List.reverseRecOn with l ih <;> simp_all +decide [ List.foldl ] ;
        grind;
      exact Nat.add_le_add_left ( h_foldl_le ‹_› ) _

/-- The attainment invariant propagates to the fixpoint, following the `h_1_iter_fix` recursion. -/
lemma h1_attained_invariant_iter {n : ℕ} (prob : PlanningTask n) (s : State' n)
    (bef : Vector (WithTop ℕ) n) (hbef : h1_attained_invariant prob s bef) :
    h1_attained_invariant prob s (h_1_iter_fix n prob bef) := by
  rw [h_1_iter_fix]
  split
  · exact hbef
  · exact h1_attained_invariant_iter prob s (h_1_step n prob bef)
      (h1_attained_invariant_step prob s bef hbef)
termination_by bef
decreasing_by exact h_1_step_lex_decreasing prob bef ‹_›

/-
**Fixpoint attainment** (reverse of `fixpoint_get_le_action_cost`).  At the `h_1` fixpoint
reached from `h_1_base n s`, every discovered fact `i` that is not already true in `s` is *attained*
by some applicable action that adds it: its value equals that action's cost plus the maximum of its
precondition values.
-/
lemma fixpoint_get_attained {n : ℕ} (prob : PlanningTask n) (s : State' n)
    (i : Fin n)
    (hi : ((h_1_iter_fix n prob (h_1_base n s))[i]).isSome)
    (hnb : s[i] = false) :
    ∃ a, a ∈ prob.actions' ∧ ∃ (hadd : i ∈ a.add'.toList)
      (happ : applicable' a (vec_to_state n (h_1_iter_fix n prob (h_1_base n s))) = true),
      ((h_1_iter_fix n prob (h_1_base n s))[i]).getD 0 = actionContribUB (h_1_iter_fix n prob (h_1_base n s)) a := by
        convert h1_attained_invariant_iter prob s ( h_1_base n s ) ( h1_attained_invariant_base prob s ) i hi using 1;
        constructor;
        · grind;
        · rintro ( h | ⟨ a, ha, happ, hadd, h ⟩ );
          · aesop;
          · refine' ⟨ a, ha, hadd, happ, le_antisymm _ h ⟩;
            convert fixpoint_get_le_action_cost prob ( h_1_iter_fix n prob ( h_1_base n s ) ) ( h_1_iter_fix_is_fixpoint n prob ( h_1_base n s ) ) a ha i hadd happ _ using 1;
            grind +suggestions;
            · exact actionContribUB_eq_of_applicable _ _ happ;
            · exact hi

/-- If a is applicable at the fixpoint, all preconditions are isSome. -/
lemma applicable_implies_pre_isSome {n : ℕ}
    (result : Vector (WithTop ℕ) n)
    (a : Action n)
    (happ : applicable' a (vec_to_state n result) = true)
    (j : Fin n) (hj : j ∈ a.pre'.toList) :
    (result[j]).isSome = true :=
  vec_to_state_isSome_of_applicable n result a happ j hj

/-
The regressed goal for singleton [g_atom] with g_atom ∈ a.add contains a.pre.
-/
lemma regress_singleton_add_contains_pre {n : ℕ}
    (a : Action n) (g_atom : Fin n)
    (j : Fin n) (hj : j ∈ a.pre'.toList) :
    j ∈ (varset'_of_state' (regress' a (state'_of_varset' (singletonVarSet g_atom)))).toList := by
  simp_all +decide [ varset'_of_state', regress' ]

set_option maxHeartbeats 1600000 in
lemma h_1_multi_atom {n : ℕ} (prob : PlanningTask n) (g : VarSet' n) (s : State' n)
    (hlen : g.toList.length > 1) :
    h_1 (replace_goal prob g) s ≤
      (g.toList.map (fun g' => h_1 (replace_goal prob (singletonVarSet g')) s)).max
        (by intro h2; simp_all) := by
  generalize_proofs at *;
  -- Let `R := h_1_iter_fix n prob (h_1_base n s)` and `s_b := vec_to_state n R`.
  set R := h_1_iter_fix n prob (h_1_base n s)
  set s_b := vec_to_state n R;
  -- By definition of `h_1`, we know that `h_1 (replace_goal prob g) s = Vector.maxFinite R + 1` if `s_b` does not satisfy `g`.
  by_cases h_sat : satisfies' g s_b = true;
  · have h_h1_eq : h_1 (replace_goal prob g) s = ((g.toList.attach.map (fun x : { x : Fin n // x ∈ g.toList } =>
      R[x.1].get (vec_to_state_isSome_of_satisfies n R g h_sat x.1 (VarSet'.mem_toList.mp x.2)))).max (by
      aesop)) := by
        unfold h_1; simp +decide [ h_sat, h_1_iter_fix_replace_goal ] ;
        unfold replace_goal; simp +decide [ h_sat ] ;
        grind +suggestions
    generalize_proofs at *;
    have h_h1_eq : ∀ x : { x : Fin n // x ∈ g.toList }, h_1 (replace_goal prob (singletonVarSet x.val)) s = Option.get R[x.val] (by
    solve_by_elim) := by
      intro x; exact (by
      unfold h_1; simp +decide [ h_1_iter_fix_replace_goal ] ;
      split_ifs <;> simp_all +decide [ replace_goal ];
      · simp_all +decide [ singletonVarSet ];
        simp_all +decide [ toVarSet' ];
        simp_all +decide [ VarSet'.toList ];
      · simp +decide [ singletonVarSet ];
        simp +decide [ toVarSet' ];
        simp +decide [ VarSet'.toList ];
        simp +decide [ List.toFinset, List.attach ];
        rfl;
      · grind +suggestions)
    generalize_proofs at *;
    convert rfl.le using 2;
    refine' List.ext_get _ _ <;> simp +decide [ h_h1_eq ];
    exact fun i hi₁ hi₂ => h_h1_eq ⟨ _, by simp ⟩;
  · obtain ⟨ g'', hg'', hg''_not_sat ⟩ := not_satisfies'_exists g s_b h_sat;
    have h_singleton_not_sat : h_1 (replace_goal prob (singletonVarSet g'')) s = Vector.maxFinite R + 1 := by
      unfold h_1; simp_all +decide [ h_1_result_eq ] ;
      unfold replace_goal; simp +decide [ hg''_not_sat ] ;
      grind +suggestions;
    have h_singleton_not_sat : h_1 (replace_goal prob g) s = Vector.maxFinite R + 1 := by
      unfold h_1; simp +decide [ h_1_iter_fix_replace_goal, h_sat ] ;
      unfold replace_goal; aesop;
    convert List.le_max_of_mem _ using 1;
    · infer_instance;
    · infer_instance;
    · grind

lemma fixpoint_add_applicable_isSome {n : ℕ} (prob : PlanningTask n) (bef : Vector (WithTop ℕ) n)
    (hfix : h_1_step n prob bef = bef)
    (a : Action n) (ha : a ∈ prob.actions')
    (g_atom : Fin n) (hadd : g_atom ∈ a.add'.toList)
    (happ : ∀ j ∈ a.pre'.toList, (bef[j]).isSome = true) :
    (bef[g_atom]).isSome = true := by
  have := h_1_step_discovers prob bef g_atom a ha hadd happ
  rw [hfix] at this
  exact this

/-
If g_atom ∉ a.add and a is regressable through [g_atom], then g_atom is in the regressed goal.
-/
set_option maxHeartbeats 800000 in
lemma g_atom_in_regressed_goal_if_not_added {n : ℕ}
    (a : Action n) (g_atom : Fin n)
    (hadd : g_atom ∉ a.add'.toList)
    (_hreg : regressable' a (state'_of_varset' (singletonVarSet g_atom)) = true) :
    g_atom ∈ (varset'_of_state' (regress' a (state'_of_varset' (singletonVarSet g_atom)))).toList := by
  unfold regress' varset'_of_state' state'_of_varset' singletonVarSet; simp +decide [ hadd ] ;
  exact Or.inl <| by simpa using hadd;

set_option maxHeartbeats 800000 in
lemma h_1_mono_of_mem {n : ℕ} (prob : PlanningTask n) (g_atom : Fin n) (s : State' n)
    (rg : VarSet' n) (hmem : g_atom ∈ rg.toList) :
    h_1 (replace_goal prob rg) s ≥ h_1 (replace_goal prob (singletonVarSet g_atom)) s := by
  -- Let's denote the result of the h_1_iter_fix as R.
  set R := h_1_iter_fix n prob (h_1_base n s);
  -- By definition of `h_1`, we know that `h_1 (replace_goal prob rg) s` is either `Vector.maxFinite R + 1` or the maximum of the pre-costs of the atoms in `rg`.
  unfold h_1 at *; simp_all +decide [ h_1_iter_fix_replace_goal ] ;
  split_ifs <;> simp_all +decide [ replace_goal, singletonVarSet ];
  · grind +suggestions;
  · apply List.le_max_of_mem;
    refine' List.mem_map.mpr ⟨ ⟨ g_atom, _ ⟩, _, _ ⟩ <;> simp_all +decide [ toVarSet' ];
    simp +decide [ VarSet'.toList, List.attach ];
    rfl;
  · have h_max_le : ∀ i : Fin n, (R[i]).isSome → (R[i]).getD 0 ≤ Vector.maxFinite R := by
      intro i hi; exact (by
      convert Vector.le_maxFinite ( show R[i] = some ( Option.getD R[i] 0 ) from ?_ ) using 1;
      cases h : R[i] <;> simp_all +decide [ Option.getD ];
      rfl);
    unfold toVarSet'; simp +decide ;
    unfold VarSet'.toList; simp +decide [ List.attach ] ;
    grind +suggestions

/-
If the fixpoint state does not satisfy the goal `g`, then `h_1` returns the dynamic
threshold `Vector.maxFinite result + 1`.
-/
lemma h_1_eq_maxFinite_of_not_satisfies {n : ℕ} (prob : PlanningTask n) (g : VarSet' n) (s : State' n)
    (hns : ¬ satisfies' g (vec_to_state n (h_1_iter_fix n prob (h_1_base n s))) = true) :
    h_1 (replace_goal prob g) s
      = Vector.maxFinite (h_1_iter_fix n prob (h_1_base n s)) + 1 := by
  unfold h_1; simp +decide [ h_1_iter_fix_replace_goal, hns ] ;
  contrapose! hns; simp_all +decide [ replace_goal ] ;
  exact hns.choose

/-
If a fact is `⊤` (unreached) at the fixpoint and an action adds it, that action cannot be
applicable at the fixpoint state (otherwise one more step would lower the fact's value).
-/
lemma h_1_step_none_not_applicable {n : ℕ} (prob : PlanningTask n) (v : Vector (WithTop ℕ) n)
    (hfix : h_1_step n prob v = v) (g_atom : Fin n) (a : Action n) (ha : a ∈ prob.actions')
    (hadd : g_atom ∈ a.add'.toList) (hnone : v[g_atom] = ⊤) :
    applicable' a (vec_to_state n v) = false := by
  contrapose! hnone; have := h_1_step_discovers prob v g_atom a ha hadd; simp_all +decide [ Vector.getElem_map ] ;
  exact Option.isSome_iff_ne_none.mp ( this fun j hj => vec_to_state_isSome_of_applicable n v a hnone j hj ) |> fun h => by simpa [ Option.isSome_iff_ne_none ] using h;

/-
If an action is not applicable at the fixpoint state, then the regressed goal (which contains
all of the action's preconditions) is not satisfied at the fixpoint state.
-/
lemma regressed_goal_not_satisfies_of_not_applicable {n : ℕ} (a : Action n) (g : VarSet' n)
    (v : Vector (WithTop ℕ) n)
    (hnapp : applicable' a (vec_to_state n v) = false) :
    ¬ satisfies' (varset'_of_state' (regress' a (state'_of_varset' g))) (vec_to_state n v) = true := by
  -- By definition of `applicable'`, there exists a precondition `p ∈ a.pre'.val` such that `(vec_to_state n v)[p.val] = false`.
  obtain ⟨p, hp⟩ : ∃ p ∈ a.pre'.toList, (vec_to_state n v)[p.val] = false := by
    contrapose! hnapp; simp_all +decide [ applicable', satisfies' ] ;
  contrapose! hnapp; simp_all +decide [ satisfies', vec_to_state_getElem ] ;
  specialize hnapp p; simp_all +decide [ regress', state'_of_varset' ] ;

/-
When the fixpoint value at `g_atom` is defined, `h_1` for the singleton goal `{g_atom}` equals
that value.
-/
lemma h_1_singleton_eq_getD {n : ℕ} (prob : PlanningTask n) (g_atom : Fin n) (s : State' n)
    (hSome : ((h_1_iter_fix n prob (h_1_base n s))[g_atom]).isSome) :
    h_1 (replace_goal prob (singletonVarSet g_atom)) s
      = (h_1_iter_fix n prob (h_1_base n s))[g_atom].getD 0 := by
  unfold h_1; simp_all +decide [ h_1_result_eq ] ;
  split_ifs <;> simp_all +decide [ replace_goal, singletonVarSet ];
  · simp_all +decide [ toVarSet', VarSet'.toList ];
  · unfold toVarSet' at *; simp_all +decide [ VarSet'.toList, List.attach ] ;
    grind +suggestions;
  · grind +suggestions

lemma h_1_singleton_bellman_add_case1 {n : ℕ} (prob : PlanningTask n) (g_atom : Fin n) (s : State' n)
    (a : Action n) (ha : a ∈ prob.actions')
    (hadd : g_atom ∈ a.add'.toList)
    (hnotSome : (h_1_iter_fix n prob (h_1_base n s))[g_atom] = ⊤) :
    h_1 (replace_goal prob (singletonVarSet g_atom)) s ≤
      a.cost + h_1 (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' (singletonVarSet g_atom))))) s := by
  have hfix := h_1_iter_fix_is_fixpoint n prob (h_1_base n s)
  have hnapp := h_1_step_none_not_applicable prob _ hfix g_atom a ha hadd hnotSome
  have hns := regressed_goal_not_satisfies_of_not_applicable a (singletonVarSet g_atom)
    (h_1_iter_fix n prob (h_1_base n s)) hnapp
  rw [h_1_eq_maxFinite_of_not_satisfies prob _ s hns]
  have hns_single : ¬ satisfies' (singletonVarSet g_atom)
      (vec_to_state n (h_1_iter_fix n prob (h_1_base n s))) = true := by
    rw [satisfies'_singleton, vec_to_state_getElem, hnotSome]
    decide
  rw [h_1_eq_maxFinite_of_not_satisfies prob _ s hns_single]
  exact Nat.le_add_left _ _

/-
Regressing the singleton goal `{g_atom}` through an action that adds `g_atom` yields exactly the
action's precondition set.
-/
lemma regressed_singleton_eq_pre {n : ℕ} (a : Action n) (g_atom : Fin n)
    (hadd : g_atom ∈ a.add'.toList) :
    varset'_of_state' (regress' a (state'_of_varset' (singletonVarSet g_atom))) = a.pre' := by
  unfold regress' varset'_of_state';
  unfold toVarSet' singletonVarSet; simp +decide [ state'_of_varset' ] ;
  simp_all +decide [ Finset.ext_iff, List.mem_toFinset ];
  grind +suggestions

/-
Fixpoint bound: if `a` adds `g_atom` and is applicable at the fixpoint, the fixpoint value at
`g_atom` is at most `a.cost` plus the `h_1` value of `a`'s precondition set.
-/
lemma h_1_iter_fix_add_bound {n : ℕ} (prob : PlanningTask n) (s : State' n)
    (a : Action n) (ha : a ∈ prob.actions') (g_atom : Fin n) (hadd : g_atom ∈ a.add'.toList)
    (happ : applicable' a (vec_to_state n (h_1_iter_fix n prob (h_1_base n s))) = true) :
    (h_1_iter_fix n prob (h_1_base n s))[g_atom].getD 0
      ≤ a.cost + h_1 (replace_goal prob a.pre') s := by
  by_contra h_contra;
  obtain ⟨c, hc⟩ : ∃ c : ℕ, (h_1_iter_fix n prob (h_1_base n s))[g_atom] = some c := by
    cases h : ( h_1_iter_fix n prob ( h_1_base n s ) )[ g_atom ] <;> simp_all +decide [ Option.getD ];
    exact ⟨ _, rfl ⟩;
  have h_pre_cost : h_1 (replace_goal prob a.pre') s = List.foldl max 0 (List.map (fun j => (h_1_iter_fix n prob (h_1_base n s))[j.val].getD 0) a.pre'.toList) := by
    unfold h_1; simp +decide [ h_1_iter_fix_replace_goal ] ;
    split_ifs <;> simp_all +decide [ replace_goal ];
    · convert list_max_eq_foldl_max_zero _ _ using 2;
      grind +extAll;
    · unfold applicable' at happ; aesop;
  have h_fixpoint_bound : c ≤ a.cost + List.foldl max 0 (List.map (fun j => (h_1_iter_fix n prob (h_1_base n s))[j.val].getD 0) a.pre'.toList) := by
    have := fixpoint_get_le_action_cost prob (h_1_iter_fix n prob (h_1_base n s)) (h_1_iter_fix_is_fixpoint n prob (h_1_base n s)) a ha g_atom hadd happ
    convert this ( by simp +decide [ hc ] ) using 1;
    · grind;
    · convert actionContribUB_eq_of_applicable _ _ happ using 1;
  grind

lemma h_1_singleton_bellman_add_case2a {n : ℕ} (prob : PlanningTask n) (g_atom : Fin n) (s : State' n)
    (a : Action n) (ha : a ∈ prob.actions')
    (hadd : g_atom ∈ a.add'.toList)
    (hSome : ((h_1_iter_fix n prob (h_1_base n s))[g_atom]).isSome)
    (happ : applicable' a (vec_to_state n (h_1_iter_fix n prob (h_1_base n s))) = true) :
    h_1 (replace_goal prob (singletonVarSet g_atom)) s ≤
      a.cost + h_1 (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' (singletonVarSet g_atom))))) s := by
  rw [regressed_singleton_eq_pre a g_atom hadd, h_1_singleton_eq_getD prob g_atom s hSome]
  exact h_1_iter_fix_add_bound prob s a ha g_atom hadd happ
lemma h_1_singleton_bellman_add_case2b {n : ℕ} (prob : PlanningTask n) (g_atom : Fin n) (s : State' n)
    (a : Action n)
    (hSome : ((h_1_iter_fix n prob (h_1_base n s))[g_atom]).isSome)
    (hnapp : ¬ applicable' a (vec_to_state n (h_1_iter_fix n prob (h_1_base n s))) = true) :
    h_1 (replace_goal prob (singletonVarSet g_atom)) s ≤
      a.cost + h_1 (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' (singletonVarSet g_atom))))) s := by
  have hnapp' : applicable' a (vec_to_state n (h_1_iter_fix n prob (h_1_base n s))) = false := by
    simpa using hnapp
  have hns := regressed_goal_not_satisfies_of_not_applicable a (singletonVarSet g_atom)
    (h_1_iter_fix n prob (h_1_base n s)) hnapp'
  rw [h_1_eq_maxFinite_of_not_satisfies prob _ s hns, h_1_singleton_eq_getD prob g_atom s hSome]
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hSome
  simp only [hc, Option.getD_some]
  calc c ≤ Vector.maxFinite (h_1_iter_fix n prob (h_1_base n s)) := Vector.le_maxFinite hc
    _ ≤ a.cost + (Vector.maxFinite (h_1_iter_fix n prob (h_1_base n s)) + 1) := by omega
lemma h_1_singleton_bellman_add {n : ℕ} (prob : PlanningTask n) (g_atom : Fin n) (s : State' n)
    (a : Action n) (ha : a ∈ prob.actions')
    (hadd : g_atom ∈ a.add'.toList) :
    h_1 (replace_goal prob (singletonVarSet g_atom)) s ≤
      a.cost + h_1 (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' (singletonVarSet g_atom))))) s := by
  by_cases h1 : (h_1_iter_fix n prob (h_1_base n s))[g_atom] = ⊤
  · exact h_1_singleton_bellman_add_case1 prob g_atom s a ha hadd h1
  · by_cases h2 : applicable' a (vec_to_state n (h_1_iter_fix n prob (h_1_base n s))) = true
    · exact h_1_singleton_bellman_add_case2a prob g_atom s a ha hadd
        (Option.isSome_iff_ne_none.mpr h1) h2
    · exact h_1_singleton_bellman_add_case2b prob g_atom s a
        (Option.isSome_iff_ne_none.mpr h1) h2
lemma h_1_singleton_bellman {n : ℕ} (prob : PlanningTask n) (g_atom : Fin n) (s : State' n)
    (a : Action n) (ha : a ∈ prob.actions')
    (hreg : regressable' a (state'_of_varset' (singletonVarSet g_atom)) = true) :
    h_1 (replace_goal prob (singletonVarSet g_atom)) s ≤
      a.cost + h_1 (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' (singletonVarSet g_atom))))) s := by
  by_cases hadd : g_atom ∈ a.add'.toList
  · exact h_1_singleton_bellman_add prob g_atom s a ha hadd
  · have hmem := g_atom_in_regressed_goal_if_not_added a g_atom hadd hreg
    exact le_trans (h_1_mono_of_mem prob g_atom s _ hmem) (Nat.le_add_left _ _)

lemma h_1_has_invar {n : ℕ} (prob : PlanningTask n):
  h_1_heuristic_regression_invariant prob (fun p s => (h_1 p s : ℕ∞)) := by
  intro s g;
  split_ifs <;> norm_cast;
  · have := h_1_goal_aware prob g s ‹_›; aesop;
  · -- Apply the `h_1_multi_atom` lemma to conclude the proof.
    apply le_trans (Nat.cast_le.mpr (h_1_multi_atom prob g s ‹_›));
    convert List.le_max_of_mem _ using 1;
    · infer_instance;
    · infer_instance;
    · have := List.max_mem ( show g.toList.map ( fun g' => h_1 ( replace_goal prob ( singletonVarSet g' ) ) s ) ≠ [ ] from by aesop ) ; aesop;
  · obtain ⟨g_atom, hg⟩ : ∃ g_atom : Fin n, g = singletonVarSet g_atom := by
      obtain ⟨g_atom, hg⟩ : ∃ g_atom : Fin n, g.toList = [g_atom] := by
        cases h : g.toList <;> simp_all +decide [ satisfies'_iff ];
        simp_all +decide [ VarSet'.toList ];
      use g_atom;
      unfold singletonVarSet; simp +decide [ toVarSet', hg ] ;
      exact Subtype.ext <| by simpa using hg;
    convert h_1_singleton_bellman prob g_atom s using 1;
    norm_num [ ← hg ];
    norm_cast

def h_1_iter {n : ℕ} (prob : PlanningTask n) (base : Vector (WithTop ℕ) n) : ℕ → Vector (WithTop ℕ) n
  | 0 => base
  | k + 1 => h_1_step n prob (h_1_iter prob base k)

@[simp] lemma h_1_iter_zero {n : ℕ} (prob : PlanningTask n) (base : Vector (WithTop ℕ) n) :
    h_1_iter prob base 0 = base := rfl

@[simp] lemma h_1_iter_succ {n : ℕ} (prob : PlanningTask n) (base : Vector (WithTop ℕ) n) (k : ℕ) :
    h_1_iter prob base (k + 1) = h_1_step n prob (h_1_iter prob base k) := rfl

/-- One step of `h_1_iter` is componentwise `≤` the previous one. -/
lemma h_1_iter_succ_le {n : ℕ} (prob : PlanningTask n) (base : Vector (WithTop ℕ) n) (k : ℕ) (i : Fin n) :
    (h_1_iter prob base (k + 1))[i] ≤ (h_1_iter prob base k)[i] :=
  h_1_step_le n prob (h_1_iter prob base k) i

/-- `h_1_iter` is antitone in the iteration index (componentwise). -/
lemma h_1_iter_le_of_le {n : ℕ} (prob : PlanningTask n) (base : Vector (WithTop ℕ) n)
    {j k : ℕ} (h : j ≤ k) (i : Fin n) :
    (h_1_iter prob base k)[i] ≤ (h_1_iter prob base j)[i] := by
  induction k with
  | zero => simp_all
  | succ k ih =>
    rcases Nat.lt_or_ge j (k + 1) with hjk | hjk
    · exact le_trans (h_1_iter_succ_le prob base k i) (ih (by omega))
    · simp_all [Nat.le_antisymm h hjk]

/-- Once a fact becomes `isSome`, it stays `isSome` at every later iteration. -/
lemma h_1_iter_isSome_mono {n : ℕ} (prob : PlanningTask n) (base : Vector (WithTop ℕ) n)
    {j k : ℕ} (h : j ≤ k) (i : Fin n)
    (hj : ((h_1_iter prob base j)[i]).isSome) : ((h_1_iter prob base k)[i]).isSome := by
  induction k with
  | zero => simp_all
  | succ k ih =>
    rcases Nat.lt_or_ge j (k + 1) with hjk | hjk
    · exact h_1_step_preserves_isSome prob (h_1_iter prob base k) i (ih (by omega) hj)
    · simp_all [Nat.le_antisymm h hjk]

/-- If `h_1_iter` is stationary at index `K` (one step does not change it), it is stationary
forever after. -/
lemma h_1_iter_const_of_stationary {n : ℕ} (prob : PlanningTask n) (base : Vector (WithTop ℕ) n)
    {K : ℕ} (hK : h_1_iter prob base (K + 1) = h_1_iter prob base K) {k : ℕ} (hk : K ≤ k) :
    h_1_iter prob base k = h_1_iter prob base K := by
  induction k with
  | zero => simp_all
  | succ k ih =>
    rcases Nat.lt_or_ge K (k + 1) with hKk | hKk
    · have : h_1_iter prob base k = h_1_iter prob base K := ih (by omega)
      rw [h_1_iter_succ, this, ← h_1_iter_succ, hK]
    · simp_all [Nat.le_antisymm hk hKk]

/-- Applying one `h_1_step` before computing the fixpoint does not change the result. -/
lemma h_1_iter_fix_step {n : ℕ} (prob : PlanningTask n) (bef : Vector (WithTop ℕ) n) :
    h_1_iter_fix n prob (h_1_step n prob bef) = h_1_iter_fix n prob bef := by
  conv_rhs => rw [h_1_iter_fix]
  split
  · rename_i h; rw [h, h_1_iter_fix]; simp [h]
  · rfl

/-
The indexed iteration agrees with `h_1_iter_fix` once it has stabilised.
-/
lemma h_1_iter_fix_eq_iter_of_stationary {n : ℕ} (prob : PlanningTask n) (base : Vector (WithTop ℕ) n)
    {K : ℕ} (hK : h_1_iter prob base (K + 1) = h_1_iter prob base K) :
    h_1_iter_fix n prob base = h_1_iter prob base K := by
  -- By induction on K, we can show that h_1_iter_fix n prob base = h_1_iter_fix n prob (h_1_iter prob base K).
  have h_ind : ∀ K, h_1_iter_fix n prob base = h_1_iter_fix n prob (h_1_iter prob base K) := by
    intro K
    induction K with
    | zero => rfl
    | succ K ih => rw [ih, h_1_iter_succ, h_1_iter_fix_step]
  rw [h_ind K, h_1_iter_fix]
  simp_all [h_1_iter_succ]

/-
There is an iteration index `K` at which `h_1_iter` has reached the fixpoint, and it equals
`h_1_iter_fix`.
-/
lemma h_1_iter_eventually_fix {n : ℕ} (prob : PlanningTask n) (base : Vector (WithTop ℕ) n) :
    ∃ K, h_1_iter prob base K = h_1_iter_fix n prob base := by
  induction' base using h_1_iter_fix.induct with base ih;
  exact prob;
  · use 0;
    unfold h_1_iter_fix; aesop;
  · rename_i h₁ h₂;
    obtain ⟨ K, hK ⟩ := h₂;
    use K + 1;
    convert hK using 1;
    · exact Nat.recOn K rfl fun k ih => by rw [ h_1_iter_succ, ih, h_1_iter_succ ] ;
    · rw [ h_1_iter_fix ] ; aesop

/-- Every fact's value eventually stabilises at its `h_1_iter_fix` value (per coordinate). -/
lemma h_1_iter_stabilizes_at {n : ℕ} (prob : PlanningTask n) (base : Vector (WithTop ℕ) n) (i : Fin n) :
    ∃ k, (h_1_iter prob base k)[i] = (h_1_iter_fix n prob base)[i] := by
  obtain ⟨K, hK⟩ := h_1_iter_eventually_fix prob base
  exact ⟨K, by rw [hK]⟩

/-- The fixpoint value is componentwise `≤` every finite-index iterate. -/
lemma h_1_iter_fix_le_iter {n : ℕ} (prob : PlanningTask n) (base : Vector (WithTop ℕ) n) (k : ℕ)
    (i : Fin n) :
    (h_1_iter_fix n prob base)[i] ≤ (h_1_iter prob base k)[i] := by
  obtain ⟨K, hK⟩ := h_1_iter_eventually_fix prob base
  have hstat : h_1_iter prob base (K + 1) = h_1_iter prob base K := by
    rw [h_1_iter_succ, hK, h_1_iter_fix_is_fixpoint]
  rcases le_total k K with h | h
  · rw [← hK]; exact h_1_iter_le_of_le prob base h i
  · rw [← hK, h_1_iter_const_of_stationary prob base hstat h]

/-- A fact that is `isSome` at some finite-index iterate is `isSome` at the fixpoint. -/
lemma h_1_iter_fix_isSome_of_iter {n : ℕ} (prob : PlanningTask n) (base : Vector (WithTop ℕ) n) (k : ℕ)
    (i : Fin n) (h : ((h_1_iter prob base k)[i]).isSome) :
    ((h_1_iter_fix n prob base)[i]).isSome := by
  obtain ⟨K, hK⟩ := h_1_iter_eventually_fix prob base
  have hstat : h_1_iter prob base (K + 1) = h_1_iter prob base K := by
    rw [h_1_iter_succ, hK, h_1_iter_fix_is_fixpoint]
  rcases le_total k K with hkK | hKk
  · rw [← hK]; exact h_1_iter_isSome_mono prob base hkK i h
  · have : (h_1_iter prob base k)[i] = (h_1_iter_fix n prob base)[i] := by
      rw [h_1_iter_const_of_stationary prob base hstat hKk, hK]
    rwa [this] at h

open Classical in
/-- The **value-stabilisation rank** of a fact: the first iteration index at which `h_1_iter`
reaches the fixpoint value at `i`. -/
noncomputable def h_1_rank {n : ℕ} (prob : PlanningTask n) (base : Vector (WithTop ℕ) n) (i : Fin n) : ℕ :=
  Nat.find (h_1_iter_stabilizes_at prob base i)

lemma h_1_rank_spec {n : ℕ} (prob : PlanningTask n) (base : Vector (WithTop ℕ) n) (i : Fin n) :
    (h_1_iter prob base (h_1_rank prob base i))[i] = (h_1_iter_fix n prob base)[i] :=
  Nat.find_spec (h_1_iter_stabilizes_at prob base i)

lemma h_1_rank_not_before {n : ℕ} (prob : PlanningTask n) (base : Vector (WithTop ℕ) n) (i : Fin n)
    {k : ℕ} (hk : k < h_1_rank prob base i) :
    (h_1_iter prob base k)[i] ≠ (h_1_iter_fix n prob base)[i] :=
  Nat.find_min (h_1_iter_stabilizes_at prob base i) hk

lemma h_1_rank_le {n : ℕ} (prob : PlanningTask n) (base : Vector (WithTop ℕ) n) (i : Fin n)
    {k : ℕ} (hk : (h_1_iter prob base k)[i] = (h_1_iter_fix n prob base)[i]) :
    h_1_rank prob base i ≤ k :=
  Nat.find_min' (h_1_iter_stabilizes_at prob base i) hk

/-
**Rank attainment.** A fact `w` discovered at the fixpoint with *positive* stabilisation rank is
attained, at the iteration `v` just before it stabilises, by some applicable adding action `a`; and
the maximum precondition value of `a` is the *same* at `v` as at the fixpoint (so the maximising
precondition is already stabilised at `v`).  This is the inductive engine of the achievability of
`h^max` by justification-graph walks.
-/
/-
`foldl max 0` is monotone in the mapped list (pointwise `≤`).
-/
lemma foldl_max_mono {β : Type*} (l : List β) (g h : β → ℕ)
    (hgh : ∀ x ∈ l, g x ≤ h x) :
    (l.map g).foldl max 0 ≤ (l.map h).foldl max 0 := by
  induction' l using List.reverseRecOn with x l ih <;> simp_all [ List.foldl ];
  grind

/-- A value obtained by `g` from a list element is `≤` the running `foldl max 0` of the mapped
list. -/
lemma le_foldl_max_of_mem {β : Type*} (g : β → ℕ) {x : β} {l : List β} (hx : x ∈ l) :
    g x ≤ (l.map g).foldl max 0 := by
  induction' l using List.reverseRecOn with l y ih
  · exact absurd hx (List.not_mem_nil)
  · rw [List.map_append, List.foldl_append]
    rcases List.mem_append.mp hx with h | h
    · exact le_trans (ih h) (by simp [le_max_left])
    · simp only [List.mem_singleton] at h; subst h; simp [le_max_right]
set_option maxHeartbeats 1000000 in
lemma h_1_rank_attained {n : ℕ} (prob : PlanningTask n) (base : Vector (WithTop ℕ) n) (w : Fin n)
    (hw : ((h_1_iter_fix n prob base)[w]).isSome)
    (hr : 0 < h_1_rank prob base w) :
    ∃ a ∈ prob.actions',
      applicable' a (vec_to_state n (h_1_iter prob base (h_1_rank prob base w - 1))) = true ∧
      w ∈ a.add'.toList ∧
      (h_1_iter_fix n prob base)[w]
        = some (actionContribUB (h_1_iter prob base (h_1_rank prob base w - 1)) a) ∧
      (a.pre'.toList.map (fun j =>
          ((h_1_iter prob base (h_1_rank prob base w - 1))[j]).getD 0)).foldl max 0
        = (a.pre'.toList.map (fun j => ((h_1_iter_fix n prob base)[j]).getD 0)).foldl max 0 := by
  have := h_1_step_attained prob (h_1_iter prob base (h_1_rank prob base w - 1)) w ?_;
  · obtain ⟨ a, ha₁, ha₂, ha₃, ha₄ ⟩ := this; use a; simp_all +decide [ h_1_iter_succ ] ;
    have h_pre_max_eq : (h_1_iter_fix n prob base)[w] ≤ some (a.cost + List.foldl max 0 (List.map (fun j => ((h_1_iter_fix n prob base)[j.val]).getD 0) a.pre'.toList)) := by
      have h_pre_max_eq : applicable' a (vec_to_state n (h_1_iter_fix n prob base)) = true := by
        have h_pre_max_eq : ∀ j ∈ a.pre'.toList, (h_1_iter_fix n prob base)[j].isSome = true := by
          intro j hj; exact h_1_iter_fix_isSome_of_iter prob base _ _ (vec_to_state_isSome_of_applicable n (h_1_iter prob base (h_1_rank prob base w - 1)) a ha₂ j hj);
        unfold applicable' satisfies'; simp +decide [ h_pre_max_eq ] ;
        intro j hj; specialize h_pre_max_eq j; simp_all +decide [ vec_to_state_getElem ] ;
      convert fixpoint_value_le_action_cost prob (h_1_iter_fix n prob base) (h_1_iter_fix_is_fixpoint n prob base) a ha₁ w ?_ h_pre_max_eq using 1;
      · convert actionContribUB_eq_of_applicable _ _ h_pre_max_eq |> Eq.symm using 1;
        simp +decide [ actionContribUB, list_max_eq_foldl_max_zero ];
        simp +decide [ List.foldl_map ];
        grind;
      · convert ha₃ using 1;
    have h_pre_max_eq : (h_1_iter_fix n prob base)[w] = some (a.cost + List.foldl max 0 (List.map (fun j => ((h_1_iter prob base (h_1_rank prob base w - 1))[j.val]).getD 0) a.pre'.toList)) := by
      convert ha₄ using 1;
      rw [ ← h_1_rank_spec prob base w ];
      rw [ show h_1_rank prob base w = h_1_rank prob base w - 1 + 1 from by rw [ Nat.sub_add_cancel hr ] ] ; rfl;
    simp_all +decide [ WithTop.some_eq_coe ];
    exact ⟨ rfl, le_antisymm ‹_› <| by
      apply foldl_max_mono;
      intro x hx; exact (by
      have h_pre_max_eq : (h_1_iter_fix n prob base)[x] ≤ (h_1_iter prob base (h_1_rank prob base w - 1))[x] := by
        exact h_1_iter_fix_le_iter prob base _ _;
      cases h : ( h_1_iter_fix n prob base )[ x ] <;> cases h' : ( h_1_iter prob base ( h_1_rank prob base w - 1 ) )[ x ] <;> simp_all +decide [ Option.getD ];
      exact absurd ( vec_to_state_isSome_of_applicable n ( h_1_iter prob base ( h_1_rank prob base w - 1 ) ) a ha₂ x ( by simpa using hx ) ) ( by simp +decide [ h' ] )) ⟩;
  · have h_diff : (h_1_iter prob base (h_1_rank prob base w))[w] ≠ (h_1_iter prob base (h_1_rank prob base w - 1))[w] := by
      grind +suggestions;
    cases k : h_1_rank prob base w <;> aesop

theorem h_1_admissible {n : ℕ} (prob : PlanningTask n) :
  heur_admissible prob (fun s => (h_1 prob s : ℕ∞)) :=
    admissible_of_h_1_regression_invariant prob (fun p s => (h_1 p s : ℕ∞)) (h_1_has_invar prob) prob.goal'

/-
For each action `a` adding `i`: if `a` is applicable under the larger vector `w` then it is also
applicable under the smaller `v`, and its `actionContribUB` is smaller under `v`.
-/
lemma actionContribUB_mono_of_applicable {n : ℕ} {v w : Vector (WithTop ℕ) n}
    (h : ∀ i : Fin n, v[i] ≤ w[i]) (a : Action n)
    (haw : applicable' a (vec_to_state n w) = true) :
    applicable' a (vec_to_state n v) = true ∧ actionContribUB v a ≤ actionContribUB w a := by
  have h_applicable : ∀ j ∈ a.pre'.toList, (v[j]).isSome = true := by
    intros j hj; exact (by
    have := vec_to_state_isSome_of_applicable n w a haw j hj; have := h j; cases h : v[j] <;> cases h' : w[j] <;> aesop;);
  refine' ⟨ _, _ ⟩;
  · unfold applicable';
    grind +suggestions;
  · refine' add_le_add le_rfl ( foldl_max_mono _ _ _ _ );
    intro j hj; specialize h j; rcases h' : v[j] with ( _ | _ | k ) <;> rcases h'' : w[j] with ( _ | _ | l ) <;> simp_all +decide ;
    · grind +suggestions;
    · cases h;
      (expose_names; exact Nat.not_succ_le_zero k h);
    · exact Nat.le_of_succ_le_succ ( WithTop.coe_le_coe.mp h )

lemma h_1_step_mono {n : ℕ} (prob : PlanningTask n) {v w : Vector (WithTop ℕ) n}
    (h : ∀ i : Fin n, v[i] ≤ w[i]) (i : Fin n) :
    (h_1_step n prob v)[i] ≤ (h_1_step n prob w)[i] := by
  by_contra h_contra;
  obtain ⟨a, ha⟩ : ∃ a ∈ prob.actions', applicable' a (vec_to_state n w) = true ∧ i ∈ a.add'.toList ∧ (h_1_step n prob w)[i] = some (actionContribUB w a) := by
    by_cases h_eq : (h_1_step n prob w)[i] = w[i];
    · exact False.elim <| h_contra <| le_trans ( h_1_step_le n prob v i ) <| h i |> le_trans <| h_eq.ge;
    · exact h_1_step_attained prob w i h_eq;
  obtain ⟨h_applicable, h_contribution⟩ : applicable' a (vec_to_state n v) = true ∧ actionContribUB v a ≤ actionContribUB w a := by
    exact actionContribUB_mono_of_applicable h a ha.2.1;
  have h_min_le : (h_1_step n prob v)[i] ≤ some (actionContribUB v a) := by
    convert h_1_step_le_action_contribution prob v a ha.1 i ha.2.2.1 h_applicable using 1;
    rw [ actionContribUB_eq_of_applicable v a h_applicable ];
    split_ifs <;> simp_all +decide [ List.foldl_map ];
    · grind;
    · rw [ list_max_eq_foldl_max_zero ];
      rw [ List.foldl_map ];
  exact h_contra <| h_min_le.trans <| WithTop.coe_le_coe.mpr h_contribution |> le_trans <| by aesop;

lemma h_1_iter_fix_ge_of_postfixpoint {n : ℕ} (prob : PlanningTask n)
    (base w : Vector (WithTop ℕ) n) (hw : ∀ i : Fin n, w[i] ≤ (h_1_step n prob w)[i])
    (hle : ∀ i : Fin n, w[i] ≤ base[i]) (i : Fin n) :
    w[i] ≤ (h_1_iter_fix n prob base)[i] := by
  have h_ind : ∀ k, ∀ j : Fin n, w[j] ≤ (h_1_iter prob base k)[j] := by
    intro k
    induction' k with k ih
    · simpa [h_1_iter] using hle
    · intro j
      exact le_trans (hw j) (le_trans (h_1_step_mono prob ih j) (by simp [h_1_iter]))
  obtain ⟨ K, hK ⟩ := h_1_iter_eventually_fix prob base
  specialize h_ind K i
  rwa [hK] at h_ind
lemma h_1_iter_fix_ge_of_fixpoint {n : ℕ} (prob : PlanningTask n)
    (base w : Vector (WithTop ℕ) n) (hw : h_1_step n prob w = w)
    (hle : ∀ i : Fin n, w[i] ≤ base[i]) (i : Fin n) :
    w[i] ≤ (h_1_iter_fix n prob base)[i] :=
  h_1_iter_fix_ge_of_postfixpoint prob base w (fun j => (congrArg (·[j]) hw).ge) hle i

/-
**Post-fixpoint criterion for `h_1_step`.**  If, for every action `a` that adds the fact `i` and
is applicable at the state induced by `bef`, some precondition `q` of `a` satisfies
`bef[i] ≤ some a.cost + bef[q]`, then `bef[i] ≤ (h_1_step n prob bef)[i]`, i.e. `bef` is a
post-fixpoint at `i`.  (Since `h_1_step` is always `≤ bef`, this means `bef` is in fact a fixpoint at
`i`.)  This is the action-level Bellman criterion that makes a candidate vector a valid lower bound
for the `h^max` fixpoint.
-/
lemma h_1_step_ge_of_action_bound {n : ℕ} (prob : PlanningTask n) (bef : Vector (WithTop ℕ) n)
    (i : Fin n)
    (h : ∀ a ∈ prob.actions', i ∈ a.add'.toList → applicable' a (vec_to_state n bef) = true →
      ∃ q ∈ a.pre'.toList, bef[i] ≤ (a.cost : WithTop ℕ) + bef[q]) :
    bef[i] ≤ (h_1_step n prob bef)[i] := by
  contrapose! h; simp_all +decide [ h_1_step_getElem_contrib ] ;
  obtain ⟨a, ha⟩ : ∃ a ∈ prob.actions', applicable' a (vec_to_state n bef) = true ∧ i ∈ a.add'.toList ∧ (h_1_step n prob bef)[i] = some (actionContribUB bef a) := by
    have := h_1_step_attained prob bef i ( by aesop ) ; aesop;
  refine' ⟨ a, ha.1, _, ha.2.1, _ ⟩ <;> simp_all +decide [ actionContribUB ];
  intro q hq; refine' lt_of_le_of_lt _ h;
  have h_foldl_le : ∀ {l : List (Fin n)}, q ∈ l → Option.getD bef[q] 0 ≤ List.foldl max 0 (List.map (fun j => Option.getD bef[j] 0) l) := by
    intros l hl; induction' l using List.reverseRecOn with l ih <;> aesop;
  cases h : bef[q] <;> simp_all +decide [ WithTop.some_eq_coe ];
  · have := vec_to_state_isSome_of_applicable n bef a ha.2.1 q ( by simpa using hq ) ; simp_all +decide [ vec_to_state_getElem ] ;
  · convert h_foldl_le ( show q ∈ a.pre'.toList from by simpa using hq ) using 1

/-! ### `isSome`/discovery pattern depends only on the actions' fields (not on costs)

The `h^max` fixpoint discovers a fact (`isSome`) iff that fact is delete-relaxation reachable, which
depends only on the actions' preconditions and add-effects and on the initial value vector — not on
the action costs.  The following lemmas make this precise: two problems whose action lists have the
same length and pairwise-equal preconditions and add-effects produce the **same `isSome` pattern**
at every iteration, hence at the fixpoint. -/

/-
Two value vectors with the same `isSome` pattern induce the same boolean state.
-/
lemma vec_to_state_eq_of_isSome_eq {n : ℕ} (bef1 bef2 : Vector (WithTop ℕ) n)
    (h : ∀ i : Fin n, (bef1[i]).isSome = (bef2[i]).isSome) :
    vec_to_state n bef1 = vec_to_state n bef2 := by
  ext i;
  convert h ⟨ i, by assumption ⟩ using 1;
  · convert vec_to_state_getElem n bef1 ⟨ i, by assumption ⟩ using 1;
  · convert vec_to_state_getElem n bef2 ⟨ i, by assumption ⟩ using 1

/-
`h_1_step` discovers fact `i` iff it was already discovered or some applicable action adds it.
-/
lemma h_1_step_isSome_iff {n : ℕ} (prob : PlanningTask n) (bef : Vector (WithTop ℕ) n) (i : Fin n) :
    ((h_1_step n prob bef)[i]).isSome = true ↔
      (bef[i]).isSome = true ∨
        ∃ a ∈ prob.actions', i ∈ a.add'.toList ∧ applicable' a (vec_to_state n bef) = true := by
  -- By definition of `h_1_step`, we can rewrite the left-hand side of the equivalence.
  rw [h_1_step_getElem];
  simp +zetaDelta at *;
  split_ifs <;> simp_all +decide [ updateIfCheaper_isSome ]; all_goals grind

/-
The `isSome` pattern of `h_1_step` depends only on the actions' preconditions and add-effects.
If `prob1` and `prob2` have the same number of actions with pairwise equal preconditions and
add-effects, and `bef1`, `bef2` induce the same state, then one `h_1_step` gives the same `isSome`
pattern.
-/
lemma h_1_step_isSome_eq_of_fields {n : ℕ} (prob1 prob2 : PlanningTask n)
    (hlen : prob1.actions'.length = prob2.actions'.length)
    (hpre : ∀ i (h1 : i < prob1.actions'.length) (h2 : i < prob2.actions'.length),
       prob1.actions'[i].pre = prob2.actions'[i].pre)
    (hadd : ∀ i (h1 : i < prob1.actions'.length) (h2 : i < prob2.actions'.length),
       prob1.actions'[i].add = prob2.actions'[i].add)
    (bef1 bef2 : Vector (WithTop ℕ) n)
    (hstate : vec_to_state n bef1 = vec_to_state n bef2)
    (i : Fin n) :
    ((h_1_step n prob1 bef1)[i]).isSome = ((h_1_step n prob2 bef2)[i]).isSome := by
  -- Apply the `h_1_step_isSome_iff` lemma to both `prob1` and `prob2`.
  have h1 := h_1_step_isSome_iff prob1 bef1 i
  have h2 := h_1_step_isSome_iff prob2 bef2 i;
  convert h1.trans ?_;
  any_goals exact Option.isSome ( h_1_step n prob2 bef2 )[ i ] = true;
  · grind;
  · rw [ h2 ];
    constructor <;> rintro ( h | ⟨ a, ha, hi, happ ⟩ );
    · have := vec_to_state_getElem n bef1 i; have := vec_to_state_getElem n bef2 i; aesop;
    · obtain ⟨ k, hk ⟩ := List.mem_iff_getElem.mp ha;
      obtain ⟨ hk₁, rfl ⟩ := hk; use Or.inr ⟨ prob2.actions'[k], by aesop, by
        have := hadd k hk₁ ( by linarith ) ; simp_all +decide [ Action.add ] ;
        exact mem_convertVarSet.mp ( this ▸ mem_convertVarSet.mpr hi ), by
        convert happ using 1;
        unfold applicable'; simp +decide [ hpre k hk₁ ( by linarith ), hadd k hk₁ ( by linarith ), hstate ] ;
        have := hpre k hk₁ ( by linarith ) ; have := hadd k hk₁ ( by linarith ) ; simp_all +decide [ Action.pre, Action.add ] ;
        simp_all +decide [ Set.ext_iff, satisfies' ] ⟩ ;
    · convert h using 1;
      rw [ ← vec_to_state_getElem n bef1 i, ← vec_to_state_getElem n bef2 i, hstate ];
      grind +suggestions;
    · obtain ⟨ k, hk ⟩ := List.mem_iff_getElem.mp ha;
      obtain ⟨ hk₁, hk₂ ⟩ := hk; specialize hpre k; specialize hadd k; simp_all +decide [ Action.pre, Action.add ] ;
      refine' Or.inr ⟨ prob1.actions'[k], _, _, _ ⟩ <;> simp_all +decide [ convertVarSet ];
      · exact hadd.symm.subset hi;
      · unfold applicable' at *; simp_all +decide [ Set.ext_iff ] ;

lemma h_1_iter_isSome_eq_of_fields {n : ℕ} (prob1 prob2 : PlanningTask n)
    (hlen : prob1.actions'.length = prob2.actions'.length)
    (hpre : ∀ i (h1 : i < prob1.actions'.length) (h2 : i < prob2.actions'.length),
       prob1.actions'[i].pre = prob2.actions'[i].pre)
    (hadd : ∀ i (h1 : i < prob1.actions'.length) (h2 : i < prob2.actions'.length),
       prob1.actions'[i].add = prob2.actions'[i].add)
    (base : Vector (WithTop ℕ) n) (k : ℕ) (i : Fin n) :
    ((h_1_iter prob1 base k)[i]).isSome = ((h_1_iter prob2 base k)[i]).isSome := by
      induction' k with k ih generalizing i;
      · rfl;
      · convert h_1_step_isSome_eq_of_fields prob1 prob2 hlen hpre hadd ( h_1_iter prob1 base k ) ( h_1_iter prob2 base k ) ( vec_to_state_eq_of_isSome_eq _ _ ih ) i using 1

lemma h_1_iter_fix_isSome_eq_of_fields {n : ℕ} (prob1 prob2 : PlanningTask n)
    (hlen : prob1.actions'.length = prob2.actions'.length)
    (hpre : ∀ i (h1 : i < prob1.actions'.length) (h2 : i < prob2.actions'.length),
       prob1.actions'[i].pre = prob2.actions'[i].pre)
    (hadd : ∀ i (h1 : i < prob1.actions'.length) (h2 : i < prob2.actions'.length),
       prob1.actions'[i].add = prob2.actions'[i].add)
    (base : Vector (WithTop ℕ) n) (i : Fin n)
    (h : ((h_1_iter_fix n prob1 base)[i]).isSome) :
    ((h_1_iter_fix n prob2 base)[i]).isSome := by
  obtain ⟨K1, hK1⟩ := h_1_iter_eventually_fix prob1 base
  apply h_1_iter_fix_isSome_of_iter prob2 base (max K1 0) i
  rw [← h_1_iter_isSome_eq_of_fields prob1 prob2 hlen hpre hadd base (max K1 0) i]
  apply h_1_iter_isSome_mono prob1 base (le_max_left K1 0) i
  rw [hK1]
  exact h

end STRIPS
