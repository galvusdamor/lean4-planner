
import Mathlib.Tactic.Linarith

import planning.CriticalPath
import planning.PerfectHeuristic

import planning.temp

namespace Validator

/-- If two vectors are componentwise ≤ in WithTop ℕ and differ, then the first is
    lexicographically less than the second under `withTop.lex Nat.lt`. -/
lemma vector_le_ne_implies_lex {n : ℕ} (v1 v2 : Vector (WithTop ℕ) n)
    (hle : ∀ i : Fin n, v1[i] ≤ v2[i])
    (hne : v1 ≠ v2) :
    Vector.Lex n (withTop.lex Nat.lt) v1 v2 := by
  have h_lex : ∀ (l1 l2 : List (WithTop ℕ)), (∀ i < l1.length, l1[i]! ≤ l2[i]!) → l1 ≠ l2 → l1.length = l2.length → List.Lex (withTop.lex Nat.lt) l1 l2 := by
    intros l1 l2 hle hne hlen;
    induction' l1 with x l1 ih generalizing l2 <;> induction' l2 with y l2 ih' <;> simp_all
    by_cases hxy : x = y;
    · grind +suggestions;
    · have hxy_lt : x < y := by
        refine lt_of_le_of_ne (hle 0 ?_) hxy
        linarith
      exact List.Lex.rel (by
      cases x <;> cases y <;> simp_all +decide [ withTop.lex ]);
  convert h_lex _ _ _ _ _ <;> simp_all +decide [ Vector.ext_iff ];
  exact fun i hi => hle ⟨ i, hi ⟩

/-- `h_1_step` is componentwise ≤ and when it differs, the result is lex-smaller. -/
lemma h_1_step_lex_decreasing {n : ℕ} (prob : STRIPS n) (bef : Vector (WithTop ℕ) n)
    (hne : h_1_step n prob bef ≠ bef) :
    Vector.Lex n (withTop.lex Nat.lt) (h_1_step n prob bef) bef := by
  exact vector_le_ne_implies_lex _ _ (fun i => h_1_step_le n prob bef i) hne

-- termination by the fact that h_1_step is monotone in its bef argument
def h_1_iter_fix (n : ℕ) (prob : STRIPS n) (bef : Vector (WithTop ℕ) n) : Vector (WithTop ℕ) n :=
  let next := h_1_step n prob bef
  if _forTermination : next = bef then
    bef
  else
    h_1_iter_fix n prob next
termination_by bef
decreasing_by exact h_1_step_lex_decreasing prob bef _forTermination

/-- At the fixpoint, h_1_step is idempotent. -/
lemma h_1_iter_fix_is_fixpoint (n : ℕ) (prob : STRIPS n) (bef : Vector (WithTop ℕ) n) :
    h_1_step n prob (h_1_iter_fix n prob bef) = h_1_iter_fix n prob bef := by
  rw [h_1_iter_fix]
  split
  · assumption
  · exact h_1_iter_fix_is_fixpoint n prob (h_1_step n prob bef)
termination_by bef
decreasing_by exact h_1_step_lex_decreasing prob bef ‹_›

/-- h_1_iter_fix is componentwise ≤ the input. -/
lemma h_1_iter_fix_le (n : ℕ) (prob : STRIPS n) (bef : Vector (WithTop ℕ) n) (i : Fin n) :
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
  induction l using List.reverseRecOn
  · simp_all only [List.not_mem_nil]
  · simp_all only [ge_iff_le, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    cases hmem with
    | inl h =>
      simp_all only [forall_const]
      split
      next x c_1 => simp_all only [le_sup_iff, true_or]
      next x => simp_all only
    | inr h_1 =>
      subst h_1
      simp_all

/-
Any finite value in the vector is ≤ maxFinite.
-/
lemma Vector.le_maxFinite {n : ℕ} {v : Vector (WithTop ℕ) n} {i : Fin n} {c : ℕ}
    (h : v[i] = some c) : c ≤ Vector.maxFinite v := by
  have hmem : (some c : WithTop ℕ) ∈ v.toList := by
    convert List.getElem_mem (l := v.toList) (n := i.val) (h := by simp)
    exact h.symm
  exact foldl_max_ge_elem v.toList 0 c hmem


-- h_1 effectively considers delete relaxation, using fixpoint iteration
def h_1 {n : ℕ} (prob : STRIPS n) (s : State' n) : ℕ :=
  let result := h_1_iter_fix n prob (h_1_base n s)
  let s_b := vec_to_state n result

  -- check if the goal has been reached
  if h_sat : satisfies' prob.goal' s_b then
    let pre_cost : List ℕ := prob.goal'.val.attach.map (fun x : { x : Fin n // x ∈ prob.goal'.val } =>
      result[x.1].get (by exact vec_to_state_isSome_of_satisfies n result prob.goal' h_sat x.1 x.2))

    -- cost of the action plus most expensive precondition
    if pre_cost_nil : pre_cost = [] then 0 else pre_cost.max pre_cost_nil
  else
    Vector.maxFinite result + 1 -- dynamic threshold: always ≥ any individual fixpoint value


/-- replace_goal prob g has the same actions as prob. -/
lemma replace_goal_actions' {n : ℕ} (prob : STRIPS n) (g : VarSet' n) :
    (replace_goal prob g).actions' = prob.actions' := by
  unfold replace_goal; rfl

/-- h_1_step only depends on prob.actions', so replacing the goal doesn't change it. -/
lemma h_1_step_replace_goal {n : ℕ} (prob : STRIPS n) (g : VarSet' n)
    (bef : Vector (WithTop ℕ) n) :
    h_1_step n (replace_goal prob g) bef = h_1_step n prob bef := by
  unfold h_1_step replace_goal; rfl

/-- The fixpoint result for replace_goal prob g is the same as for prob. -/
lemma h_1_iter_fix_replace_goal {n : ℕ} (prob : STRIPS n) (g : VarSet' n) (bef : Vector (WithTop ℕ) n) :
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
lemma h_1_goal_aware {n : ℕ} (prob : STRIPS n) (g : VarSet' n) (s : State' n)
    (hsat : satisfies' g s = true) :
    h_1 (replace_goal prob g) s = 0 := by
  revert @hsat;
  unfold h_1
  simp [ satisfies', replace_goal ]
  intro hsat
  have h_result : ∀ i : Fin n, i ∈ g.val → (h_1_iter_fix n { varNames := prob.varNames, actions' := prob.actions', init' := prob.init', goal' := g } (h_1_base n s))[i] = some 0 := by
     intro i hi
     have h_base : (h_1_base n s)[i] = some 0 := by
       unfold h_1_base
       simp_all only [Fin.getElem_fin, Vector.getElem_map, Vector.getElem_finRange, Fin.eta, ↓reduceIte]
     have h_iter : (h_1_iter_fix n { varNames := prob.varNames, actions' := prob.actions', init' := prob.init', goal' := g } (h_1_base n s))[i] ≤ some 0 := by
        exact h_1_iter_fix_le n { varNames := prob.varNames, actions' := prob.actions', init' := prob.init', goal' := g } ( h_1_base n s ) i |> le_trans <| h_base.le
     have h_zero : (h_1_iter_fix n { varNames := prob.varNames, actions' := prob.actions', init' := prob.init', goal' := g } (h_1_base n s))[i] = some 0 := by
        cases h : ( h_1_iter_fix n { varNames := prob.varNames, actions' := prob.actions', init' := prob.init', goal' := g } ( h_1_base n s ) )[i] <;> simp_all [ WithTop.some_eq_coe ]
     exact h_zero;
  split_ifs <;> simp_all [ vec_to_state ]
  rename_i h;
  obtain ⟨ i, hi, hi' ⟩ := h;
  have h_contra : (h_1_iter_fix n { varNames := prob.varNames, actions' := prob.actions', init' := prob.init', goal' := g } (h_1_base n s))[i].isSome = true := by
                                      grind;
  have h_contra : (vec_to_state n (h_1_iter_fix n { varNames := prob.varNames, actions' := prob.actions', init' := prob.init', goal' := g } (h_1_base n s)))[i.val] = true := by
    convert h_contra using 1
    apply vec_to_state_getElem n _ i
  unfold vec_to_state at h_contra
  simp_all only [Bool.true_eq_false]

/-
If satisfies' g state holds and i ∈ g, then state[i] = true.
-/
lemma satisfies'_mem {n : ℕ} (g : VarSet' n) (state : State' n) (i : Fin n)
    (hsat : satisfies' g state = true) (hmem : i ∈ g.val) :
    state[i.val] = true := by
  contrapose! hsat; simp_all +decide [ satisfies', List.all_eq_true ] ;
  use i

/-
satisfies' for a singleton [g_atom] is equivalent to state[g_atom] = true.
-/
lemma satisfies'_singleton {n : ℕ} (g_atom : Fin n) (state : State' n) :
    satisfies' ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩ state = true ↔ state[g_atom.val] = true := by
  rw [ satisfies' ];
  simp_all only [Fin.getElem_fin, List.all_cons, List.all_nil, Bool.and_true]

/-
If i ∈ g and satisfies' g state, then satisfies' [i] state.
-/
lemma satisfies'_singleton_of_mem {n : ℕ} (g : VarSet' n) (state : State' n) (i : Fin n)
    (hsat : satisfies' g state = true) (hmem : i ∈ g.val) :
    satisfies' ⟨[i], by simp [List.SortedLT, StrictMono]⟩ state = true := by
  unfold satisfies' at *;
  grind

/-
If ¬ satisfies' g state, then there exists i ∈ g with state[i] = false.
-/
lemma not_satisfies'_exists {n : ℕ} (g : VarSet' n) (state : State' n)
    (hsat : ¬ satisfies' g state = true) :
    ∃ i ∈ g.val, state[i.val] = false := by
  contrapose! hsat; simp_all +decide [ satisfies', List.all_eq_true ] ;

/-- The result vector for h_1 is the same regardless of the goal. -/
lemma h_1_result_eq {n : ℕ} (prob : STRIPS n) (g : VarSet' n) (s : State' n) :
    h_1_iter_fix n (replace_goal prob g) (h_1_base n s) = h_1_iter_fix n prob (h_1_base n s) :=
  h_1_iter_fix_replace_goal prob g (h_1_base n s)

/-
h_1_step at position i is bounded by any applicable action's cost contribution.
    This does NOT need the fixpoint assumption.
-/
lemma h_1_step_le_action_contribution {n : ℕ} (prob : STRIPS n)
    (bef : Vector (WithTop ℕ) n)
    (a : Action n) (ha : a ∈ prob.actions')
    (i : Fin n) (hadd : i ∈ a.add'.val)
    (happ : applicable' a (vec_to_state n bef) = true) :
    (h_1_step n prob bef)[i] ≤ some (
      if h : a.pre'.val.attach.map (fun x : { x : Fin n // x ∈ a.pre'.val } =>
        bef[x.1].get (vec_to_state_isSome_of_applicable n bef a happ x.1 x.2)) = []
      then a.cost
      else a.cost + (a.pre'.val.attach.map (fun x =>
        bef[x.1].get (vec_to_state_isSome_of_applicable n bef a happ x.1 x.2))).max h) := by
  erw [ Array.getElem_map ];
  simp +zetaDelta at *;
  split_ifs;
  · grind;
  · grind;
  · refine' le_trans _ ( WithTop.coe_le_coe.mpr <| show a.cost ≥ _ from _ );
    convert updateIfCheaper_le_newCost _ _;
    exact List.min_le_of_mem ( List.mem_filterMap.mpr ⟨ a, by simp_all only [not_forall, ↓reduceIte, ↓reduceDIte, and_self] ⟩ );
  · refine' le_trans _ ( WithTop.coe_le_coe.mpr _ );
    convert updateIfCheaper_le_newCost _ _;
    refine' List.min_le_of_mem _;
    grind

/-- At the fixpoint, result[i] ≤ any applicable action's cost contribution. -/
lemma fixpoint_value_le_action_cost {n : ℕ} (prob : STRIPS n)
    (result : Vector (WithTop ℕ) n)
    (hfix : h_1_step n prob result = result)
    (a : Action n) (ha : a ∈ prob.actions')
    (i : Fin n) (hadd : i ∈ a.add'.val)
    (happ : applicable' a (vec_to_state n result) = true) :
    result[i] ≤ some (
      if h : a.pre'.val.attach.map (fun x : { x : Fin n // x ∈ a.pre'.val } =>
        result[x.1].get (vec_to_state_isSome_of_applicable n result a happ x.1 x.2)) = []
      then a.cost
      else a.cost + (a.pre'.val.attach.map (fun x =>
        result[x.1].get (vec_to_state_isSome_of_applicable n result a happ x.1 x.2))).max h) := by
  have := h_1_step_le_action_contribution prob result a ha i hadd happ
  rwa [show (h_1_step n prob result)[i] = result[i] from congr_arg (·[i]) hfix] at this

/-
At the fixpoint, if a is applicable and i ∈ a.add', then result[i].get ≤ action cost + max precondition costs.
    Uses List.foldl to compute the max precondition cost to avoid non-emptiness proofs.
-/
lemma fixpoint_get_le_action_cost {n : ℕ} (prob : STRIPS n)
    (result : Vector (WithTop ℕ) n)
    (hfix : h_1_step n prob result = result)
    (a : Action n) (ha : a ∈ prob.actions')
    (i : Fin n) (hadd : i ∈ a.add'.val)
    (happ : applicable' a (vec_to_state n result) = true)
    (hi : (result[i]).isSome) :
    (result[i]).get hi ≤
      a.cost + a.pre'.val.attach.foldl (fun acc (x : { x : Fin n // x ∈ a.pre'.val }) =>
        max acc ((result[x.1]).get (vec_to_state_isSome_of_applicable n result a happ x.1 x.2))) 0 := by
  convert fixpoint_value_le_action_cost prob result hfix a ha i hadd happ using 1;
  split_ifs <;> simp_all +decide
  · have h_eq : result[i] ≤ some a.cost := by
      grind +suggestions;
    simp_all +singlePass [ WithTop.le_def ];
    obtain ⟨ a, b, hab, h₁, h₂ ⟩ := h_eq; simp_all +decide [ WithTop.some_eq_coe ] ;
    exact le_add_right hab;
  · rw [ ← WithTop.coe_le_coe ];
    congr! 1;
    · exact Option.some_get _;
    · have h_foldl_eq_max : ∀ (l : List ℕ) (h : l ≠ []), List.foldl (fun acc x => max acc x) 0 l = l.max h := by
        intros l hl_nonempty
        induction' l using List.reverseRecOn with l ih;
        · contradiction;
        · cases l <;> simp_all +decide [ List.max ];
      convert congr_arg ( fun x : ℕ => some ( a.cost + x ) ) ( h_foldl_eq_max _ _ ) using 1;
      rw [ List.foldl_map ];
      rfl
/-- Upper-bound contribution of an action `a` at a value vector `v`, using `getD 0` so that no
applicability/`isSome` proof is needed.  When `a` is applicable in `vec_to_state n v` (so every
precondition value `isSome`), `(v[j]).getD 0 = (v[j]).get _`, so this matches the `attach`/`get`
form used by `fixpoint_get_le_action_cost`. -/
def actionContribUB {n : ℕ} (v : Vector (WithTop ℕ) n) (a : Action n) : ℕ :=
  a.cost + (a.pre'.val.map (fun j => (v[j]).getD 0)).foldl max 0

/-
When `a` is applicable in `vec_to_state n v`, `actionContribUB` (the `getD`-based form) coincides
with the `attach`/`get`-based contribution used inside `h_1_step` and `fixpoint_get_le_action_cost`,
because every precondition value is then `isSome` (so `getD 0 = get`).
-/
lemma actionContribUB_eq_of_applicable {n : ℕ} (v : Vector (WithTop ℕ) n) (a : Action n)
    (happ : applicable' a (vec_to_state n v) = true) :
    actionContribUB v a =
      a.cost + a.pre'.val.attach.foldl (fun acc (x : { x : Fin n // x ∈ a.pre'.val }) =>
        max acc ((v[x.1]).get (vec_to_state_isSome_of_applicable n v a happ x.1 x.2))) 0 := by
  simp +decide [ actionContribUB, List.foldl_map ];
  rw [ ← List.foldl_map ];
  convert rfl using 2;
  rw [ ← List.foldl_map ] ; congr! 2;
  refine' List.ext_get _ _ <;> simp +decide [ List.get ];
  grind +suggestions

/-
`actionContribUB`-based restatement of `h_1_step_getElem`: the per-index value of `h_1_step`,
with the inline precondition-max replaced by `actionContribUB` (valid since the action is applicable
in the relevant branch).  This removes the dependent precondition proofs, leaving a plain
`filterMap`/`min`/`updateIfCheaper` term.
-/
lemma h_1_step_getElem_contrib {n : ℕ} (prob : STRIPS n) (v : Vector (WithTop ℕ) n) (i : Fin n) :
    (h_1_step n prob v)[i] =
      (let L : List ℕ := prob.actions'.filterMap (fun a =>
        if i ∈ a.add'.val then
          if applicable' a (vec_to_state n v) then .some (actionContribUB v a) else .none
        else .none);
      if hL : L = [] then v[i] else updateIfCheaper (L.min hL) v[i]) := by
  rw [h_1_step_getElem];
  unfold actionContribUB; simp +decide [ List.foldl_map ] ;
  congr! 3;
  · congr! 2;
    split_ifs <;> simp_all +decide [ List.foldl_map ];
    convert rfl using 2;
    have h_foldl_eq_max : ∀ (l : List ℕ) (h : l ≠ []), List.foldl (fun acc x => max acc x) 0 l = l.max h := by
      intros l hl_nonempty
      induction' l using List.reverseRecOn with l ih;
      · contradiction;
      · cases l <;> simp_all +decide [ List.max ];
    convert h_foldl_eq_max _ _ using 2;
    rw [ ← List.foldl_map ] ; congr! 2;
    grind +extAll;
  · grind

/-
If `h_1_step` strictly changes the value at `i`, the new value is exactly some applicable
adding-action's `actionContribUB` (the action that attained the minimum).
-/
lemma h_1_step_attained {n : ℕ} (prob : STRIPS n) (v : Vector (WithTop ℕ) n) (i : Fin n)
    (h_ne : (h_1_step n prob v)[i] ≠ v[i]) :
    ∃ a ∈ prob.actions', applicable' a (vec_to_state n v) = true ∧ i ∈ a.add'.val ∧
      (h_1_step n prob v)[i] = some (actionContribUB v a) := by
  -- Since $h ne$, we know that the $i$-th element of the $h_1_step$ result is exactly some value, and we need to find the corresponding action.
  obtain ⟨a, ha⟩ : ∃ a ∈ prob.actions', applicable' a (vec_to_state n v) = true ∧ i ∈ a.add'.val ∧ (h_1_step n prob v)[i] = some (actionContribUB v a) := by
    have hL_nonempty : (prob.actions'.filterMap (fun a => if i ∈ a.add'.val then if applicable' a (vec_to_state n v) then some (actionContribUB v a) else none else none)) ≠ [] := by
      contrapose! h_ne;
      rw [ h_1_step_getElem_contrib, h_ne ] ; simp +decide [ updateIfCheaper ]
    rw [ h_1_step_getElem_contrib ] at *;
    have h_min_mem : (List.min (List.filterMap (fun a => if i ∈ a.add'.val then if applicable' a (vec_to_state n v) then some (actionContribUB v a) else none else none) prob.actions') hL_nonempty) ∈ List.filterMap (fun a => if i ∈ a.add'.val then if applicable' a (vec_to_state n v) then some (actionContribUB v a) else none else none) prob.actions' := by
      exact List.min_mem hL_nonempty;
    grind +suggestions;
  use a

/-- Iteration invariant for fixpoint attainment: every discovered fact is either already true in `s`
(value `0` from the base) or has its value bounded **below** by some currently-applicable action that
adds it.  Together with `fixpoint_get_le_action_cost` (the matching upper bound) this pins the value
to an action contribution at the fixpoint. -/
def h1_attained_invariant {n : ℕ} (prob : STRIPS n) (s : State' n)
    (v : Vector (WithTop ℕ) n) : Prop :=
  ∀ i : Fin n, (v[i]).isSome → s[i] = true ∨
    ∃ a ∈ prob.actions', applicable' a (vec_to_state n v) = true ∧ i ∈ a.add'.val ∧
      (v[i]).getD 0 ≥ actionContribUB v a

/-
The base vector satisfies the attainment invariant: it is `some 0` exactly at the facts true in
`s`, and `none` elsewhere, so `isSome` forces the `s[i] = true` disjunct.
-/
lemma h1_attained_invariant_base {n : ℕ} (prob : STRIPS n) (s : State' n) :
    h1_attained_invariant prob s (h_1_base n s) := by
  intro i hi; by_cases hi' : s[i.val] = true <;> simp_all +decide [ h_1_base ] ;

/-
`h_1_step` preserves the attainment invariant.  Values only decrease (`h_1_step_le`) and
applicability only grows (`h_1_step_preserves_isSome`), so an action witnessing the invariant at `v`
still witnesses it (with a no-larger contribution) at `h_1_step n prob v`; an entry whose value
strictly dropped was set to the minimum action contribution, witnessed by the minimiser action.
-/
set_option maxHeartbeats 1000000 in
lemma h1_attained_invariant_step {n : ℕ} (prob : STRIPS n) (s : State' n)
    (v : Vector (WithTop ℕ) n) (hv : h1_attained_invariant prob s v) :
    h1_attained_invariant prob s (h_1_step n prob v) := by
  intro i hi; by_cases h_cases : ( h_1_step n prob v )[i] = v[i] <;> simp_all +decide [ h1_attained_invariant, h_1_step_preserves_isSome ] ;
  · rcases hv i hi with h | ⟨ a, ha₁, ha₂, ha₃, ha₄ ⟩ <;> simp_all +decide [ actionContribUB ];
    refine Or.inr ⟨ a, ha₁, ?_, ha₃, ?_ ⟩;
    · unfold applicable';
      unfold satisfies';
      grind +suggestions;
    · refine le_trans ?_ ha₄;
      have h_monotone : ∀ j ∈ a.pre'.val, (h_1_step n prob v)[j].getD 0 ≤ v[j].getD 0 := by
        intro j hj; specialize h_cases; have := h_1_step_le n prob v j; simp_all +decide [ Vector.getElem_map ] ;
        cases h : ( h_1_step n prob v )[ j ] <;> cases h' : v[ j ] <;> simp_all +decide [ WithTop.some_eq_coe ];
        · exact absurd ( vec_to_state_isSome_of_applicable n v a ha₂ j hj ) ( by simp +decide [ h', vec_to_state ] );
        · exact this;
      have h_monotone_foldl : ∀ (l : List (Fin n)), (∀ j ∈ l, (h_1_step n prob v)[j].getD 0 ≤ v[j].getD 0) → List.foldl max 0 (List.map (fun j => (h_1_step n prob v)[j].getD 0) l) ≤ List.foldl max 0 (List.map (fun j => v[j].getD 0) l) := by
        intros l hl; induction' l using List.reverseRecOn with l ih <;> simp_all +decide [ List.foldl ] ;
        induction' l using List.reverseRecOn with l ih <;> simp_all +decide [ List.foldl ];
        grind;
      convert Nat.add_le_add_left ( h_monotone_foldl _ _ ) a.cost using 1;
      exact h_monotone;
  · obtain ⟨ a, ha₁, ha₂, ha₃, ha₄ ⟩ := h_1_step_attained prob v i h_cases; use Or.inr ⟨ a, ha₁, ?_, ha₃, ?_ ⟩ <;> simp_all +decide [ actionContribUB ] ;
    · -- Since `a` is applicable in `v`, it remains applicable in `h_1_step n prob v` because `h_1_step` preserves `isSome`.
      have h_applicable : ∀ j : Fin n, j ∈ a.pre'.val → (vec_to_state n (h_1_step n prob v))[j.val] = true := by
        intro j hj; exact vec_to_state_getElem n _ j |> fun h => h.symm ▸ h_1_step_preserves_isSome prob v j ( vec_to_state_isSome_of_applicable n v a ha₂ j hj ) ;
      unfold applicable'; simp_all +decide [ satisfies', List.all_eq_true ] ;
    · have h_monotone : ∀ j ∈ a.pre'.val, (h_1_step n prob v)[j].getD 0 ≤ v[j].getD 0 := by
        intros j hj; exact (by
        have h_monotone : (h_1_step n prob v)[j] ≤ v[j] := by
          exact h_1_step_le n prob v j;
        cases h : ( h_1_step n prob v )[j] <;> cases h' : v[j] <;> simp_all +decide [ WithTop.le_def ];
        · exact absurd ( vec_to_state_isSome_of_applicable n v a ha₂ j hj ) ( by simp +decide [ h', vec_to_state ] );
        · exact h_monotone);
      have h_monotone : ∀ (l : List (Fin n)), (∀ j ∈ l, (h_1_step n prob v)[j].getD 0 ≤ v[j].getD 0) → List.foldl max 0 (List.map (fun j => (h_1_step n prob v)[j].getD 0) l) ≤ List.foldl max 0 (List.map (fun j => v[j].getD 0) l) := by
        intros l hl; induction' l using List.reverseRecOn with l ih <;> simp_all +decide [ List.foldl ] ;
        induction' l using List.reverseRecOn with l ih <;> simp_all +decide [ List.foldl ];
        grind;
      convert h_monotone ( a.pre'.val.map ( fun j => j ) ) _ using 1 <;> simp_all +decide [ List.map_map ]

/-- The attainment invariant propagates to the fixpoint, following the `h_1_iter_fix` recursion. -/
lemma h1_attained_invariant_iter {n : ℕ} (prob : STRIPS n) (s : State' n)
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
lemma fixpoint_get_attained {n : ℕ} (prob : STRIPS n) (s : State' n)
    (i : Fin n)
    (hi : ((h_1_iter_fix n prob (h_1_base n s))[i]).isSome)
    (hnb : s[i] = false) :
    ∃ a, a ∈ prob.actions' ∧ ∃ (hadd : i ∈ a.add'.val)
      (happ : applicable' a (vec_to_state n (h_1_iter_fix n prob (h_1_base n s))) = true),
      ((h_1_iter_fix n prob (h_1_base n s))[i]).getD 0 = actionContribUB (h_1_iter_fix n prob (h_1_base n s)) a := by
  obtain ⟨a, ha, hadd, happ, hcost⟩ : ∃ a ∈ prob.actions', applicable' a (vec_to_state n (h_1_iter_fix n prob (h_1_base n s))) = true ∧ i ∈ a.add'.val ∧ (h_1_iter_fix n prob (h_1_base n s))[i].getD 0 ≥ actionContribUB (h_1_iter_fix n prob (h_1_base n s)) a := by
    have := h1_attained_invariant_iter prob s ( h_1_base n s ) ( h1_attained_invariant_base prob s ) i; simp_all +decide [ h1_attained_invariant ] ;
  have := fixpoint_get_le_action_cost prob ( h_1_iter_fix n prob ( h_1_base n s ) ) ( h_1_iter_fix_is_fixpoint n prob ( h_1_base n s ) ) a ha i happ hadd hi; simp_all +decide [ actionContribUB ] ;
  refine' ⟨ a, ha, hadd, happ, le_antisymm _ hcost ⟩;
  convert this using 1;
  · exact Eq.symm (Option.get_eq_getD (h_1_iter_fix n prob (h_1_base n s))[↑i]);
  · convert actionContribUB_eq_of_applicable _ _ hadd using 1

/-- If a is applicable at the fixpoint, all preconditions are isSome. -/
lemma applicable_implies_pre_isSome {n : ℕ}
    (result : Vector (WithTop ℕ) n)
    (a : Action n)
    (happ : applicable' a (vec_to_state n result) = true)
    (j : Fin n) (hj : j ∈ a.pre'.val) :
    (result[j]).isSome = true :=
  vec_to_state_isSome_of_applicable n result a happ j hj

/-
The regressed goal for singleton [g_atom] with g_atom ∈ a.add' contains a.pre'.
-/
lemma regress_singleton_add_contains_pre {n : ℕ}
    (a : Action n) (g_atom : Fin n)
    (j : Fin n) (hj : j ∈ a.pre'.val) :
    j ∈ (varset'_of_state' (regress' a (state'_of_varset' ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩))).val := by
  unfold regress'
  grind +suggestions

/-
For multi-atom goals, h_1(g, s) ≤ max of singletons.
-/
set_option maxHeartbeats 400000 in
lemma h_1_multi_atom {n : ℕ} (prob : STRIPS n) (g : VarSet' n) (s : State' n)
    (hlen : g.1.length > 1) :
    h_1 (replace_goal prob g) s ≤
      (g.1.map (fun g' => h_1 (replace_goal prob ⟨[g'], by simp [List.SortedLT, StrictMono]⟩) s)).max
        (by intro h2; simp_all) := by
  unfold h_1;
  simp +decide [ h_1_iter_fix_replace_goal ];
  split_ifs <;> simp_all +decide [ replace_goal ];
  case neg h h_1 =>
    -- Since the goal is satisfied, each singleton goal must also be satisfied.
    have h_singleton_satisfied : ∀ g' ∈ g.val, satisfies' ⟨[g'], by simp [List.SortedLT, StrictMono]⟩ (vec_to_state n (h_1_iter_fix n prob (h_1_base n s))) = true :=
      fun g' a => satisfies'_singleton_of_mem (replace_goal prob g).goal'
                    (vec_to_state n (h_1_iter_fix n prob (h_1_base n s))) g' h a
    simp_all +decide [ List.max ];
    congr! 2;
    refine' List.ext_get _ _
    · simp_all only [gt_iff_lt, List.length_map, List.length_attach]
    · intro n_1 h₁ h₂
      simp_all only [gt_iff_lt, List.get_eq_getElem, List.getElem_map, List.getElem_attach, List.getElem_mem, ↓reduceDIte]
  · -- Since the goal state does not satisfy [g'], the maximum of the list is at least the maximum of the singletons.
    have h_max_ge_singletons : ∃ g' ∈ g.val, satisfies' ⟨[g'], by simp [List.SortedLT, StrictMono]⟩ (vec_to_state n (h_1_iter_fix n prob (h_1_base n s))) = false := by
      grind +suggestions;
    refine' lt_of_lt_of_le _ ( show _ ≥ Vector.maxFinite ( h_1_iter_fix n prob ( h_1_base n s ) ) + 1 from _ );
    · exact Nat.lt_succ_self _;
    · refine' List.le_max_of_mem _;
      grind

/-- At the fixpoint, if g_atom ∈ a.add' and a is applicable, then result[g_atom] is Some. -/
lemma fixpoint_add_applicable_isSome {n : ℕ} (prob : STRIPS n) (bef : Vector (WithTop ℕ) n)
    (hfix : h_1_step n prob bef = bef)
    (a : Action n) (ha : a ∈ prob.actions')
    (g_atom : Fin n) (hadd : g_atom ∈ a.add'.val)
    (happ : ∀ j ∈ a.pre'.val, (bef[j]).isSome = true) :
    (bef[g_atom]).isSome = true := by
  have := h_1_step_discovers prob bef g_atom a ha hadd happ
  rw [hfix] at this
  exact this

/-
If g_atom ∉ a.add' and a is regressable through [g_atom], then g_atom is in the regressed goal.
-/
set_option maxHeartbeats 800000 in
lemma g_atom_in_regressed_goal_if_not_added {n : ℕ}
    (a : Action n) (g_atom : Fin n)
    (hadd : g_atom ∉ a.add'.val)
    (_hreg : regressable' a (state'_of_varset' ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩) = true) :
    g_atom ∈ (varset'_of_state' (regress' a (state'_of_varset' ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩))).val := by
  unfold regress' at *; simp_all only [Fin.getElem_fin]
  unfold regressable' at _hreg
  simp_all only [Fin.getElem_fin, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.decide_or,
    Bool.decide_eq_false, Bool.decide_eq_true, List.all_eq_true, Bool.or_eq_true]
  unfold varset'_of_state';
  simp +decide [ BitVec.getElem_cast, BitVec.getElem_ofBoolListLE ];
  grind +suggestions

/-
If g_atom ∈ rg.val and the result vector is the same, then h_1(rg, s) ≥ h_1([g_atom], s).
-/
lemma h_1_mono_of_mem {n : ℕ} (prob : STRIPS n) (g_atom : Fin n) (s : State' n)
    (rg : VarSet' n) (hmem : g_atom ∈ rg.val) :
    h_1 (replace_goal prob rg) s ≥ h_1 (replace_goal prob ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩) s := by
  have h_simp : h_1_iter_fix n (replace_goal prob rg) (h_1_base n s) = h_1_iter_fix n prob (h_1_base n s) ∧ h_1_iter_fix n (replace_goal prob ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩) (h_1_base n s) = h_1_iter_fix n prob (h_1_base n s) := by
    exact ⟨ h_1_iter_fix_replace_goal prob rg ( h_1_base n s ), h_1_iter_fix_replace_goal prob ⟨ [ g_atom ], by simp [ List.SortedLT, StrictMono ] ⟩ ( h_1_base n s ) ⟩
  unfold h_1; simp +decide [ h_simp ] ;
  split_ifs <;> simp_all +decide [ replace_goal ];
  · apply List.le_max_of_mem; simp
    exact ⟨ g_atom, hmem, rfl ⟩;
  · simp +decide [ List.max ];
    exact Nat.le_succ_of_le ( Vector.le_maxFinite ( h_1_iter_fix n prob ( h_1_base n s ) |> fun x => x[g_atom] |> fun y => by
      simp_all only [Fin.getElem_fin, Option.some_get]
      rfl ) );
  · rename_i h₁ h₂ h₃
    generalize_proofs at *; (
    contrapose! h₃; simp_all +decide [ satisfies' ] ;
    exact h₁ _ hmem)

/-
Case 1: g_atom not discovered at the fixpoint.
-/
lemma h_1_singleton_bellman_add_case1 {n : ℕ} (prob : STRIPS n) (g_atom : Fin n) (s : State' n)
    (a : Action n) (ha : a ∈ prob.actions')
    (hadd : g_atom ∈ a.add'.val)
    (hnotSome : (h_1_iter_fix n prob (h_1_base n s))[g_atom] = ⊤) :
    h_1 (replace_goal prob ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩) s ≤
      a.cost + h_1 (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩)))) s := by
  -- Since `g_atom` is not discovered at the fixpoint, `h_1` returns `Vector.maxFinite result + 1`.
  have h_h1_new_g_atom : h_1 (replace_goal prob ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩) s = Vector.maxFinite (h_1_iter_fix n prob (h_1_base n s)) + 1 := by
    -- Since `g_atom` is not discovered at the fixpoint, `h_1` returns `Vector.maxFinite result + 1` by definition.
    simp [h_1]
    split_ifs <;> simp_all
    · simp_all +decide [ replace_goal ]
    · rename_i h₁ h₂;
      erw [ satisfies'_singleton ] at h₁ ; simp_all +decide [ vec_to_state_getElem ];
      exact absurd h₁ ( by erw [ h_1_iter_fix_replace_goal ] ; simp_all only [Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] ; rfl);
    · rw [ h_1_iter_fix_replace_goal ];
  have h_not_discover_j : ∃ j ∈ a.pre'.val, (h_1_iter_fix n prob (h_1_base n s))[j] = ⊤ := by
    contrapose! hnotSome;
    convert fixpoint_add_applicable_isSome prob ( h_1_iter_fix n prob ( h_1_base n s ) ) ( h_1_iter_fix_is_fixpoint n prob ( h_1_base n s ) ) a ha g_atom hadd _;
    · cases h : ( h_1_iter_fix n prob ( h_1_base n s ) )[g_atom]
      · simp_all only [Fin.getElem_fin, ne_eq, not_true_eq_false, false_iff, Bool.not_eq_true, Option.isSome_eq_false_iff,
      Option.isNone_iff_eq_none]
        rfl
      · simp_all only [Fin.getElem_fin, ne_eq, WithTop.coe_ne_top, not_false_eq_true, true_iff]
        rfl
    · exact fun j hj => by
        specialize hnotSome j hj; cases h : ( h_1_iter_fix n prob ( h_1_base n s ) )[j]
        · simp_all only [ne_eq, not_true_eq_false]
        · simp_all only [ne_eq, WithTop.coe_ne_top, not_false_eq_true, Fin.getElem_fin]
          rfl
  obtain ⟨ j, hj₁, hj₂ ⟩ := h_not_discover_j;
  have h_j_in_rg : j ∈ (varset'_of_state' (regress' a (state'_of_varset' ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩))).val := regress_singleton_add_contains_pre a g_atom j hj₁
  have h_h1_new_rg : h_1 (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩)))) s = Vector.maxFinite (h_1_iter_fix n prob (h_1_base n s)) + 1 := by
    unfold h_1;
    simp +decide [ h_1_iter_fix_replace_goal ];
    intro h; have := satisfies'_mem _ _ _ h h_j_in_rg; simp_all +decide [ vec_to_state_getElem ] ;
  linarith

/-
Case 2a: g_atom discovered, action a applicable at fixpoint.
-/
set_option maxHeartbeats 800000 in
lemma h_1_singleton_bellman_add_case2a {n : ℕ} (prob : STRIPS n) (g_atom : Fin n) (s : State' n)
    (a : Action n) (ha : a ∈ prob.actions')
    (hadd : g_atom ∈ a.add'.val)
    (hSome : ((h_1_iter_fix n prob (h_1_base n s))[g_atom]).isSome)
    (happ : applicable' a (vec_to_state n (h_1_iter_fix n prob (h_1_base n s))) = true) :
    h_1 (replace_goal prob ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩) s ≤
      a.cost + h_1 (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩)))) s := by
  -- Let result = h_1_iter_fix n prob (h_1_base n s).
  set result := h_1_iter_fix n prob (h_1_base n s);
  have h_foldl_le_max : a.pre'.val.attach.foldl (fun acc (x : { x : Fin n // x ∈ a.pre'.val }) => max acc ((result[x.1]).get (vec_to_state_isSome_of_applicable n result a happ x.1 x.2))) 0 ≤ h_1 (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩)))) s := by
    have h_foldl_le_max : ∀ x ∈ a.pre'.val.attach, ((result[x.1]).get (vec_to_state_isSome_of_applicable n result a happ x.1 x.2)) ≤ h_1 (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩)))) s := by
      intro x hx
      have h_mem : x.1 ∈ (varset'_of_state' (regress' a (state'_of_varset' ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩))).val := by
        apply regress_singleton_add_contains_pre a g_atom x.1 x.2;
      have := h_1_mono_of_mem prob x.1 s (varset'_of_state' (regress' a (state'_of_varset' ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩))) ?_;
      · refine le_trans ?_ this;
        unfold h_1;
        simp +decide [ h_1_iter_fix_replace_goal ];
        split_ifs <;> simp_all +decide [ replace_goal ];
        · exact le_rfl;
        · exact Nat.le_succ_of_le ( Vector.le_maxFinite ( h := by simp_all only [Fin.getElem_fin, Option.some_get, result] ; simp_all only [result] ; rfl ) );
      · exact h_mem;
    have h_foldl_le_max : ∀ {l : List { x : Fin n // x ∈ a.pre'.val }}, (∀ x ∈ l, ((result[x.1]).get (vec_to_state_isSome_of_applicable n result a happ x.1 x.2)) ≤ h_1 (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩)))) s) → List.foldl (fun acc (x : { x : Fin n // x ∈ a.pre'.val }) => max acc ((result[x.1]).get (vec_to_state_isSome_of_applicable n result a happ x.1 x.2))) 0 l ≤ h_1 (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩)))) s := by
      intros l hl; induction' l using List.reverseRecOn with l ih
      · simp_all only [Fin.getElem_fin, List.mem_attach, forall_const, Subtype.forall, List.not_mem_nil, IsEmpty.forall_iff, implies_true, List.foldl_nil, zero_le, result]
      · simp_all only [Fin.getElem_fin, List.mem_attach, forall_const, Subtype.forall, implies_true, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.foldl_append, List.foldl_cons, List.foldl_nil, sup_le_iff, and_self, result]
    exact h_foldl_le_max ‹_›;
  have h_result_le : (result[g_atom]).get hSome ≤ a.cost + a.pre'.val.attach.foldl (fun acc (x : { x : Fin n // x ∈ a.pre'.val }) => max acc ((result[x.1]).get (vec_to_state_isSome_of_applicable n result a happ x.1 x.2))) 0 := by
    apply fixpoint_get_le_action_cost;
    exacts [ h_1_iter_fix_is_fixpoint n prob ( h_1_base n s ), ha, hadd, happ ];
  have h_result_eq : h_1 (replace_goal prob ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩) s = (result[g_atom]).get hSome := by
    have h_satisfies : satisfies' ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩ (vec_to_state n result) = true := by
      convert vec_to_state_getElem n result g_atom using 1;
      · unfold satisfies'
        simp_all only [Fin.getElem_fin, List.all_cons, List.all_nil, Bool.and_true, result]
      · exact hSome.symm;
    unfold h_1;
    simp +decide [ replace_goal ];
    split_ifs ; simp_all +decide [ List.max ];
    · congr! 1;
      convert h_1_iter_fix_replace_goal prob ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩ (h_1_base n s) |> congr_arg (fun x => x[g_atom]) using 1;
    · rename_i h;
      contrapose! h;
      convert h_satisfies using 1;
      congr! 2;
      convert h_1_iter_fix_replace_goal prob ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩ (h_1_base n s) using 1;
  grind +splitIndPred

/-
Case 2b: g_atom discovered, action a NOT applicable at fixpoint.
-/
lemma h_1_singleton_bellman_add_case2b {n : ℕ} (prob : STRIPS n) (g_atom : Fin n) (s : State' n)
    (a : Action n)
    (hSome : ((h_1_iter_fix n prob (h_1_base n s))[g_atom]).isSome)
    (hnapp : ¬ applicable' a (vec_to_state n (h_1_iter_fix n prob (h_1_base n s))) = true) :
    h_1 (replace_goal prob ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩) s ≤
      a.cost + h_1 (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩)))) s := by
  have h_not_applicable : ∃ j ∈ a.pre'.val, (h_1_iter_fix n prob (h_1_base n s))[j].isSome = false := by
    simp_all +decide [ applicable' ];
    contrapose! hnapp; simp_all +decide [ satisfies', vec_to_state_getElem ] ;
  obtain ⟨ j, hj₁, hj₂ ⟩ := h_not_applicable
  have h_j_in_rg : j ∈ (varset'_of_state' (regress' a (state'_of_varset' ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩))).val := by
    apply regress_singleton_add_contains_pre a g_atom j hj₁;
  have h_h_1_rg : h_1 (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩)))) s = Vector.maxFinite (h_1_iter_fix n prob (h_1_base n s)) + 1 := by
    unfold h_1;
    simp +decide [ h_1_iter_fix_replace_goal ];
    intro h; have := satisfies'_mem _ _ _ h h_j_in_rg; simp_all +decide [ vec_to_state_getElem ] ;
  have h_h_1_g_atom : h_1 (replace_goal prob ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩) s = (h_1_iter_fix n prob (h_1_base n s))[g_atom].get hSome := by
    unfold h_1;
    simp +decide [ h_1_iter_fix_replace_goal ];
    split_ifs <;> simp_all +decide [ replace_goal ];
    · rfl;
    · unfold satisfies' at *; simp_all +decide [ vec_to_state_getElem ] ;
      grind;
  have h_h_1_g_atom_le_maxFinite : (h_1_iter_fix n prob (h_1_base n s))[g_atom].get hSome ≤ Vector.maxFinite (h_1_iter_fix n prob (h_1_base n s)) := by
    apply_rules [ Vector.le_maxFinite ];
    grind;
  linarith

/-- For singleton goals with g_atom ∈ a.add', h_1 satisfies the bellman bound. -/
lemma h_1_singleton_bellman_add {n : ℕ} (prob : STRIPS n) (g_atom : Fin n) (s : State' n)
    (a : Action n) (ha : a ∈ prob.actions')
    (hadd : g_atom ∈ a.add'.val) :
    h_1 (replace_goal prob ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩) s ≤
      a.cost + h_1 (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩)))) s := by
  let result := h_1_iter_fix n prob (h_1_base n s)
  cases hcase : result[g_atom] with
  | top => exact h_1_singleton_bellman_add_case1 prob g_atom s a ha hadd hcase
  | coe c =>
    have hSome : (result[g_atom]).isSome = true := by rw [hcase]; rfl
    by_cases happ : applicable' a (vec_to_state n result) = true
    · exact h_1_singleton_bellman_add_case2a prob g_atom s a ha hadd hSome happ
    · exact h_1_singleton_bellman_add_case2b prob g_atom s a hSome happ

/-- For singleton goals, h_1 satisfies the pointwise bellman bound. -/
lemma h_1_singleton_bellman {n : ℕ} (prob : STRIPS n) (g_atom : Fin n) (s : State' n)
    (a : Action n) (ha : a ∈ prob.actions')
    (hreg : regressable' a (state'_of_varset' ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩) = true) :
    h_1 (replace_goal prob ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩) s ≤
      a.cost + h_1 (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩)))) s := by
  by_cases hadd : g_atom ∈ a.add'.val
  · exact h_1_singleton_bellman_add prob g_atom s a ha hadd
  · calc h_1 (replace_goal prob ⟨[g_atom], _⟩) s
        ≤ h_1 (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' ⟨[g_atom], _⟩)))) s :=
          h_1_mono_of_mem prob g_atom s _ (g_atom_in_regressed_goal_if_not_added a g_atom hadd hreg)
      _ ≤ a.cost + _ := Nat.le_add_left _ _

set_option maxHeartbeats 800000 in
lemma h_1_has_invar {n : ℕ} (prob : STRIPS n):
  h_1_heuristic_regression_invariant prob h_1 := by
  intro s g
  show _
  split_ifs with hsat hlen
  · exact h_1_goal_aware prob g s hsat
  · exact h_1_multi_atom prob g s hlen
  · push_neg at hlen
    intro a ha hreg
    rcases g with ⟨l, hl⟩
    cases l with
    | nil => simp [satisfies'] at hsat
    | cons g' t =>
      cases t with
      | nil => exact h_1_singleton_bellman prob g' s a ha hreg
      | cons => exfalso; simp [List.length] at hlen

/-! ### Indexed iteration of `h_1_step`

`h_1_iter_fix` is defined by well-founded recursion until a fixpoint is reached, which makes
reasoning about *when* a fact is first discovered awkward.  We introduce an explicit indexed
iteration `h_1_iter prob base k` (the `k`-fold application of `h_1_step`), prove the basic
monotonicity facts, and connect it back to `h_1_iter_fix`.  This is the foundation for a
"discovery-rank" argument: a fact discovered at iteration `k+1` has all the preconditions of its
attaining action discovered by iteration `k`. -/

/-- The `k`-fold application of `h_1_step` to a base vector. -/
def h_1_iter {n : ℕ} (prob : STRIPS n) (base : Vector (WithTop ℕ) n) : ℕ → Vector (WithTop ℕ) n
  | 0 => base
  | k + 1 => h_1_step n prob (h_1_iter prob base k)

@[simp] lemma h_1_iter_zero {n : ℕ} (prob : STRIPS n) (base : Vector (WithTop ℕ) n) :
    h_1_iter prob base 0 = base := rfl

@[simp] lemma h_1_iter_succ {n : ℕ} (prob : STRIPS n) (base : Vector (WithTop ℕ) n) (k : ℕ) :
    h_1_iter prob base (k + 1) = h_1_step n prob (h_1_iter prob base k) := rfl

/-- One step of `h_1_iter` is componentwise `≤` the previous one. -/
lemma h_1_iter_succ_le {n : ℕ} (prob : STRIPS n) (base : Vector (WithTop ℕ) n) (k : ℕ) (i : Fin n) :
    (h_1_iter prob base (k + 1))[i] ≤ (h_1_iter prob base k)[i] :=
  h_1_step_le n prob (h_1_iter prob base k) i

/-- `h_1_iter` is antitone in the iteration index (componentwise). -/
lemma h_1_iter_le_of_le {n : ℕ} (prob : STRIPS n) (base : Vector (WithTop ℕ) n)
    {j k : ℕ} (h : j ≤ k) (i : Fin n) :
    (h_1_iter prob base k)[i] ≤ (h_1_iter prob base j)[i] := by
  induction k with
  | zero => simp_all
  | succ k ih =>
    rcases Nat.lt_or_ge j (k + 1) with hjk | hjk
    · exact le_trans (h_1_iter_succ_le prob base k i) (ih (by omega))
    · simp_all [Nat.le_antisymm h hjk]

/-- Once a fact becomes `isSome`, it stays `isSome` at every later iteration. -/
lemma h_1_iter_isSome_mono {n : ℕ} (prob : STRIPS n) (base : Vector (WithTop ℕ) n)
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
lemma h_1_iter_const_of_stationary {n : ℕ} (prob : STRIPS n) (base : Vector (WithTop ℕ) n)
    {K : ℕ} (hK : h_1_iter prob base (K + 1) = h_1_iter prob base K) {k : ℕ} (hk : K ≤ k) :
    h_1_iter prob base k = h_1_iter prob base K := by
  induction k with
  | zero => simp_all
  | succ k ih =>
    rcases Nat.lt_or_ge K (k + 1) with hKk | hKk
    · have : h_1_iter prob base k = h_1_iter prob base K := ih (by omega)
      rw [h_1_iter_succ, this, ← h_1_iter_succ, hK]
    · simp_all [Nat.le_antisymm hk hKk]

/-
The indexed iteration agrees with `h_1_iter_fix` once it has stabilised.
-/
lemma h_1_iter_fix_eq_iter_of_stationary {n : ℕ} (prob : STRIPS n) (base : Vector (WithTop ℕ) n)
    {K : ℕ} (hK : h_1_iter prob base (K + 1) = h_1_iter prob base K) :
    h_1_iter_fix n prob base = h_1_iter prob base K := by
  -- By induction on K, we can show that h_1_iter_fix n prob base = h_1_iter_fix n prob (h_1_iter prob base K).
  have h_ind : ∀ K, h_1_iter_fix n prob base = h_1_iter_fix n prob (h_1_iter prob base K) := by
    intro K; exact (by
    induction K <;> simp +decide [ *, h_1_iter_succ ];
    grind +suggestions);
  rw [ h_ind K, h_1_iter_fix ] ; simp_all +decide [ h_1_iter_succ ] ;

/-
There is an iteration index `K` at which `h_1_iter` has reached the fixpoint, and it equals
`h_1_iter_fix`.
-/
lemma h_1_iter_eventually_fix {n : ℕ} (prob : STRIPS n) (base : Vector (WithTop ℕ) n) :
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
lemma h_1_iter_stabilizes_at {n : ℕ} (prob : STRIPS n) (base : Vector (WithTop ℕ) n) (i : Fin n) :
    ∃ k, (h_1_iter prob base k)[i] = (h_1_iter_fix n prob base)[i] := by
  obtain ⟨K, hK⟩ := h_1_iter_eventually_fix prob base
  exact ⟨K, by rw [hK]⟩

/-- The fixpoint value is componentwise `≤` every finite-index iterate. -/
lemma h_1_iter_fix_le_iter {n : ℕ} (prob : STRIPS n) (base : Vector (WithTop ℕ) n) (k : ℕ)
    (i : Fin n) :
    (h_1_iter_fix n prob base)[i] ≤ (h_1_iter prob base k)[i] := by
  obtain ⟨K, hK⟩ := h_1_iter_eventually_fix prob base
  have hstat : h_1_iter prob base (K + 1) = h_1_iter prob base K := by
    rw [h_1_iter_succ, hK, h_1_iter_fix_is_fixpoint]
  rcases le_total k K with h | h
  · rw [← hK]; exact h_1_iter_le_of_le prob base h i
  · rw [← hK, h_1_iter_const_of_stationary prob base hstat h]

/-- A fact that is `isSome` at some finite-index iterate is `isSome` at the fixpoint. -/
lemma h_1_iter_fix_isSome_of_iter {n : ℕ} (prob : STRIPS n) (base : Vector (WithTop ℕ) n) (k : ℕ)
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
noncomputable def h_1_rank {n : ℕ} (prob : STRIPS n) (base : Vector (WithTop ℕ) n) (i : Fin n) : ℕ :=
  Nat.find (h_1_iter_stabilizes_at prob base i)

lemma h_1_rank_spec {n : ℕ} (prob : STRIPS n) (base : Vector (WithTop ℕ) n) (i : Fin n) :
    (h_1_iter prob base (h_1_rank prob base i))[i] = (h_1_iter_fix n prob base)[i] :=
  Nat.find_spec (h_1_iter_stabilizes_at prob base i)

lemma h_1_rank_not_before {n : ℕ} (prob : STRIPS n) (base : Vector (WithTop ℕ) n) (i : Fin n)
    {k : ℕ} (hk : k < h_1_rank prob base i) :
    (h_1_iter prob base k)[i] ≠ (h_1_iter_fix n prob base)[i] :=
  Nat.find_min (h_1_iter_stabilizes_at prob base i) hk

lemma h_1_rank_le {n : ℕ} (prob : STRIPS n) (base : Vector (WithTop ℕ) n) (i : Fin n)
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
set_option maxHeartbeats 1000000 in
lemma h_1_rank_attained {n : ℕ} (prob : STRIPS n) (base : Vector (WithTop ℕ) n) (w : Fin n)
    (hw : ((h_1_iter_fix n prob base)[w]).isSome)
    (hr : 0 < h_1_rank prob base w) :
    ∃ a ∈ prob.actions',
      applicable' a (vec_to_state n (h_1_iter prob base (h_1_rank prob base w - 1))) = true ∧
      w ∈ a.add'.val ∧
      (h_1_iter_fix n prob base)[w]
        = some (actionContribUB (h_1_iter prob base (h_1_rank prob base w - 1)) a) ∧
      (a.pre'.val.map (fun j =>
          ((h_1_iter prob base (h_1_rank prob base w - 1))[j]).getD 0)).foldl max 0
        = (a.pre'.val.map (fun j => ((h_1_iter_fix n prob base)[j]).getD 0)).foldl max 0 := by
  obtain ⟨a, ha, happ, hadd, hval⟩ : ∃ a ∈ prob.actions', applicable' a (vec_to_state n (h_1_iter prob base (h_1_rank prob base w - 1))) = true ∧ w ∈ a.add'.val ∧ (h_1_step n prob (h_1_iter prob base (h_1_rank prob base w - 1)))[w] = some (actionContribUB (h_1_iter prob base (h_1_rank prob base w - 1)) a) := by
    convert h_1_step_attained prob ( h_1_iter prob base ( h_1_rank prob base w - 1 ) ) w _;
    have := h_1_rank_spec prob base w;
    contrapose! this;
    convert h_1_rank_not_before prob base w ( Nat.sub_lt hr zero_lt_one ) using 1;
    cases k : h_1_rank prob base w <;> aesop;
  have h_foldl_le : List.foldl max 0 (List.map (fun j => (h_1_iter_fix n prob base)[j].getD 0) a.pre'.val) ≤ List.foldl max 0 (List.map (fun j => (h_1_iter prob base (h_1_rank prob base w - 1))[j].getD 0) a.pre'.val) := by
    have h_foldl_le : ∀ j ∈ a.pre'.val, (h_1_iter_fix n prob base)[j].getD 0 ≤ (h_1_iter prob base (h_1_rank prob base w - 1))[j].getD 0 := by
      intros j hj
      have h_le : (h_1_iter_fix n prob base)[j] ≤ (h_1_iter prob base (h_1_rank prob base w - 1))[j] := by
        obtain ⟨ K, hK ⟩ := h_1_iter_eventually_fix prob base
        generalize_proofs at *; (
        rw [ ← hK ];
        apply h_1_iter_le_of_le; exact Nat.sub_le_of_le_add (by
        exact Nat.le_succ_of_le ( h_1_rank_le prob base w ( by aesop ) )))
      generalize_proofs at *; (
      cases h : ( h_1_iter_fix n prob base )[ j ] <;> cases h' : ( h_1_iter prob base ( h_1_rank prob base w - 1 ) )[ j ] <;> simp_all +decide [ Option.getD ];
      have := vec_to_state_isSome_of_applicable n ( h_1_iter prob base ( h_1_rank prob base w - 1 ) ) a happ j hj; simp_all +decide [ vec_to_state_getElem ] ;);
    have h_foldl_le : ∀ {l : List (Fin n)}, (∀ j ∈ l, (h_1_iter_fix n prob base)[j].getD 0 ≤ (h_1_iter prob base (h_1_rank prob base w - 1))[j].getD 0) → List.foldl max 0 (List.map (fun j => (h_1_iter_fix n prob base)[j].getD 0) l) ≤ List.foldl max 0 (List.map (fun j => (h_1_iter prob base (h_1_rank prob base w - 1))[j].getD 0) l) := by
      intros l hl; induction' l using List.reverseRecOn with l ih <;> simp_all +decide [ List.foldl ] ;
      induction' l using List.reverseRecOn with l ih <;> simp_all +decide [ List.foldl ];
      grind;
    exact h_foldl_le ‹_›;
  have h_foldl_ge : (h_1_iter_fix n prob base)[w].get hw ≤ a.cost + List.foldl max 0 (List.map (fun j => (h_1_iter_fix n prob base)[j].getD 0) a.pre'.val) := by
    have h_foldl_ge : applicable' a (vec_to_state n (h_1_iter_fix n prob base)) = true := by
      have h_applicable : ∀ j ∈ a.pre'.val, (h_1_iter_fix n prob base)[j].isSome = true := by
        intros j hj
        have h_applicable : (h_1_iter prob base (h_1_rank prob base w - 1))[j].isSome = true := by
          exact vec_to_state_isSome_of_applicable n _ _ happ _ hj;
        have h_applicable : ∀ k ≥ h_1_rank prob base w - 1, (h_1_iter prob base k)[j].isSome = true := by
          exact fun k hk => h_1_iter_isSome_mono prob base hk j h_applicable;
        obtain ⟨ K, hK ⟩ := h_1_iter_eventually_fix prob base;
        grind +suggestions;
      unfold applicable'; simp_all +decide [ vec_to_state_getElem ] ;
      unfold satisfies'; simp_all +decide [ vec_to_state_getElem ] ;
    convert fixpoint_get_le_action_cost prob ( h_1_iter_fix n prob base ) ( h_1_iter_fix_is_fixpoint n prob base ) a ha w hadd h_foldl_ge hw using 1;
    convert actionContribUB_eq_of_applicable _ _ h_foldl_ge using 1;
  have h_foldl_eq : (h_1_iter_fix n prob base)[w] = some (a.cost + List.foldl max 0 (List.map (fun j => (h_1_iter prob base (h_1_rank prob base w - 1))[j].getD 0) a.pre'.val)) := by
    convert hval using 1;
    rw [ ← h_1_rank_spec prob base w ];
    rw [ ← h_1_iter_succ ] ; congr ; omega;
  simp_all +decide [ actionContribUB ];
  exact ⟨ a, ha, happ, hadd, rfl, le_antisymm h_foldl_ge h_foldl_le ⟩
theorem h_1_admissible {n : ℕ} (prob : STRIPS n) :
  heur_admissible prob (h_1 prob) :=
    admissible_of_h_1_regression_invariant prob h_1 (h_1_has_invar prob) prob.goal'
/-
`foldl max 0` is monotone in the mapped list (pointwise `≤`).
-/
lemma foldl_max_mono {β : Type*} (l : List β) (g h : β → ℕ)
    (hgh : ∀ x ∈ l, g x ≤ h x) :
    (l.map g).foldl max 0 ≤ (l.map h).foldl max 0 := by
  induction' l using List.reverseRecOn with x l ih <;> simp_all +decide [ List.foldl ];
  grind

/-
For each action `a` adding `i`: if `a` is applicable under the larger vector `w` then it is also
applicable under the smaller `v`, and its `actionContribUB` is smaller under `v`.
-/
lemma actionContribUB_mono_of_applicable {n : ℕ} {v w : Vector (WithTop ℕ) n}
    (h : ∀ i : Fin n, v[i] ≤ w[i]) (a : Action n)
    (haw : applicable' a (vec_to_state n w) = true) :
    applicable' a (vec_to_state n v) = true ∧ actionContribUB v a ≤ actionContribUB w a := by
  constructor;
  · unfold applicable' at *; simp_all +decide [ vec_to_state_getElem ] ;
    unfold satisfies' at *; simp_all +decide [ vec_to_state_getElem ] ;
    intro x hx; specialize h x; specialize haw x hx; cases h' : v[x] <;> cases h'' : w[x] <;> simp_all +decide ;
    exact Option.isSome_of_mem rfl;
  · unfold applicable' at haw; simp_all +decide [ vec_to_state_getElem ] ;
    unfold actionContribUB; simp_all +decide [ satisfies' ] ;
    apply foldl_max_mono;
    intro x hx; specialize h x; cases h' : v[x] <;> cases h'' : w[x] <;> simp_all +decide [ Option.getD ] ;
    specialize haw x hx; simp_all +decide [ vec_to_state_getElem ] ;

set_option maxHeartbeats 400000 in
/--
`h_1_step` is monotone in its value vector: smaller (cheaper / more-reached) inputs yield smaller
outputs.  Cheaper preconditions give cheaper action contributions, and more facts being `isSome`
only makes more actions applicable.
-/
lemma h_1_step_mono {n : ℕ} (prob : STRIPS n) {v w : Vector (WithTop ℕ) n}
    (h : ∀ i : Fin n, v[i] ≤ w[i]) (i : Fin n) :
    (h_1_step n prob v)[i] ≤ (h_1_step n prob w)[i] := by
  rw [ h_1_step_getElem_contrib, h_1_step_getElem_contrib ];
  by_cases hL : List.filterMap ( fun a => if i ∈ a.add'.val then if applicable' a ( vec_to_state n v ) = true then some ( actionContribUB v a ) else none else none ) prob.actions' = [] <;> by_cases hL' : List.filterMap ( fun a => if i ∈ a.add'.val then if applicable' a ( vec_to_state n w ) = true then some ( actionContribUB w a ) else none else none ) prob.actions' = [] <;> simp +decide [ hL, hL' ];
  · exact h i;
  · obtain ⟨ a, ha ⟩ := List.length_pos_iff_exists_mem.mp ( List.length_pos_iff.mpr hL' ) ; simp_all +decide [ List.mem_filterMap ] ;
    obtain ⟨ a, ha₁, ha₂, ha₃, rfl ⟩ := ha; specialize hL a ha₁ ha₂; simp_all +decide [ applicable' ] ;
    contrapose! hL; simp_all +decide [ satisfies' ] ;
    intro x hx; specialize ha₃ x hx; specialize h x; simp_all +decide [ vec_to_state_getElem ] ;
    cases h' : v[x] <;> cases h'' : w[x] <;> simp_all +decide [ Option.isSome ];
  · refine' le_trans _ ( h i );
    exact updateIfCheaper_le _ _;
  · -- Since `Lv.min ≤ Lw.min` and `v[i] ≤ w[i]`, we can conclude by a small case split on `v[i]`, `w[i]`.
    have h_min_le : List.min (List.filterMap (fun a => if i ∈ a.add'.val then if applicable' a (vec_to_state n v) = true then some (actionContribUB v a) else none else none) prob.actions') hL ≤ List.min (List.filterMap (fun a => if i ∈ a.add'.val then if applicable' a (vec_to_state n w) = true then some (actionContribUB w a) else none else none) prob.actions') hL' := by
      have h_min_le : ∀ x ∈ List.filterMap (fun a => if i ∈ a.add'.val then if applicable' a (vec_to_state n w) = true then some (actionContribUB w a) else none else none) prob.actions', ∃ y ∈ List.filterMap (fun a => if i ∈ a.add'.val then if applicable' a (vec_to_state n v) = true then some (actionContribUB v a) else none else none) prob.actions', y ≤ x := by
        simp +zetaDelta at *;
        intros x a ha hi hw hx
        obtain ⟨ha', ha''⟩ := actionContribUB_mono_of_applicable (fun i => h i) a hw
        use a
        aesop;
      have := List.min_mem hL';
      obtain ⟨ y, hy₁, hy₂ ⟩ := h_min_le _ this;
      exact le_trans ( List.min_le_of_mem hy₁ ) hy₂;
    cases h : v[i] <;> cases h' : w[i] <;> simp_all +decide [ updateIfCheaper ];
    · exact WithTop.coe_le_coe.mpr h_min_le;
    · exact absurd ( ‹∀ i : Fin n, v[i] ≤ w[i]› i ) ( by simp +decide [ h, h' ] );
    · split_ifs <;> simp_all +decide [ WithTop.some_eq_coe ];
      exact le_trans ‹_› h_min_le;
    · split_ifs <;> norm_cast at *;
      · exact WithTop.coe_le_coe.mpr h_min_le;
      · rename_i k hk₁ hk₂;
        exact WithTop.coe_le_coe.mpr ( le_trans hk₁.le ( Nat.cast_le.mp ( h ▸ h' ▸ k i ) ) );
      · exact WithTop.coe_le_coe.mpr ( le_trans ( le_of_not_gt ‹_› ) h_min_le );
      · exact_mod_cast h ▸ h' ▸ ‹∀ i : Fin n, v[i] ≤ w[i]› i

/-
**Fixpoint domination by deflation.** Any `h_1_step`-fixpoint `w` that lies below the starting
vector `base` also lies below the deflation limit `h_1_iter_fix … base`.  (Iterating the monotone,
deflationary `h_1_step` from `base` stays above every fixpoint it dominates.)
-/
lemma h_1_iter_fix_ge_of_fixpoint {n : ℕ} (prob : STRIPS n)
    (base w : Vector (WithTop ℕ) n) (hw : h_1_step n prob w = w)
    (hle : ∀ i : Fin n, w[i] ≤ base[i]) (i : Fin n) :
    w[i] ≤ (h_1_iter_fix n prob base)[i] := by
  -- By induction on $k$, we show that $w[i] \leq (h_1_iter prob base k)[i]$ for all $k$.
  have h_ind : ∀ k, w[i] ≤ (h_1_iter prob base k)[i] := by
    intro k; induction' k with k ih generalizing i; simp_all +decide [ h_1_iter ] ;
    convert h_1_step_mono prob ih i using 1 ; aesop;
  obtain ⟨ K, hK ⟩ := h_1_iter_eventually_fix prob base; specialize h_ind K; aesop;

/-
**Fixpoint domination by post-fixpoints.** Any `h_1_step`-post-fixpoint `w` (i.e. `w ≤ h_1_step … w`
componentwise) that lies below the starting vector `base` also lies below the deflation limit
`h_1_iter_fix … base`.  This generalises `h_1_iter_fix_ge_of_fixpoint` (a fixpoint is in particular a
post-fixpoint) and is the tool for *lower-bounding* the `h_1`/`h^max` fixpoint: exhibit a
post-fixpoint below the base and it lies below the fixpoint.
-/
lemma h_1_iter_fix_ge_of_postfixpoint {n : ℕ} (prob : STRIPS n)
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

/-
**Post-fixpoint criterion for `h_1_step`.**  If, for every action `a` that adds the fact `i` and
is applicable at the state induced by `bef`, some precondition `q` of `a` satisfies
`bef[i] ≤ some a.cost + bef[q]`, then `bef[i] ≤ (h_1_step n prob bef)[i]`, i.e. `bef` is a
post-fixpoint at `i`.  (Since `h_1_step` is always `≤ bef`, this means `bef` is in fact a fixpoint at
`i`.)  This is the action-level Bellman criterion that makes a candidate vector a valid lower bound
for the `h^max` fixpoint.
-/
lemma h_1_step_ge_of_action_bound {n : ℕ} (prob : STRIPS n) (bef : Vector (WithTop ℕ) n)
    (i : Fin n)
    (h : ∀ a ∈ prob.actions', i ∈ a.add'.val → applicable' a (vec_to_state n bef) = true →
      ∃ q ∈ a.pre'.val, bef[i] ≤ (a.cost : WithTop ℕ) + bef[q]) :
    bef[i] ≤ (h_1_step n prob bef)[i] := by
  contrapose! h;
  obtain ⟨a, ha, hadd, happ⟩ : ∃ a ∈ prob.actions', i ∈ a.add'.val ∧ applicable' a (vec_to_state n bef) = true ∧ (h_1_step n prob bef)[i] = some (actionContribUB bef a) := by
    have := h_1_step_attained prob bef i (by
    exact ne_of_lt h)
    generalize_proofs at *; (
    grind +ring)
  generalize_proofs at *; (
  use a, ha, hadd, happ.left; intro q hq; have := vec_to_state_isSome_of_applicable n bef a happ.left q hq; simp_all +decide [ vec_to_state_getElem ] ;
  cases h' : bef[q] <;> simp_all +decide [ actionContribUB ];
  refine' lt_of_le_of_lt _ h;
  have h_foldl_ge : ∀ {l : List (Fin n)}, (∀ j ∈ l, (bef[j].getD 0) ≤ List.foldl max 0 (List.map (fun j => (bef[j].getD 0)) l)) := by
    intros l j hj; induction' l using List.reverseRecOn with l ih <;> simp_all +decide [ List.foldl ] ;
    grind
  generalize_proofs at *; (
  exact WithTop.coe_le_coe.mpr ( Nat.add_le_add_left ( by simpa [ h' ] using h_foldl_ge q hq ) _ )))

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
The `isSome` pattern of `h_1_step` depends only on the actions' preconditions and add-effects.
If `prob1` and `prob2` have the same number of actions with pairwise equal preconditions and
add-effects, and `bef1`, `bef2` induce the same state, then one `h_1_step` gives the same `isSome`
pattern.
-/
lemma h_1_step_isSome_eq_of_fields {n : ℕ} (prob1 prob2 : STRIPS n)
    (hlen : prob1.actions'.length = prob2.actions'.length)
    (hpre : ∀ i (h1 : i < prob1.actions'.length) (h2 : i < prob2.actions'.length),
       prob1.actions'[i].pre' = prob2.actions'[i].pre')
    (hadd : ∀ i (h1 : i < prob1.actions'.length) (h2 : i < prob2.actions'.length),
       prob1.actions'[i].add' = prob2.actions'[i].add')
    (bef1 bef2 : Vector (WithTop ℕ) n)
    (hstate : vec_to_state n bef1 = vec_to_state n bef2)
    (i : Fin n) :
    ((h_1_step n prob1 bef1)[i]).isSome = ((h_1_step n prob2 bef2)[i]).isSome := by
  by_cases h : ∃ a ∈ prob1.actions', i ∈ a.add'.val ∧ applicable' a (vec_to_state n bef1) = true;
  · obtain ⟨ a, ha₁, ha₂, ha₃ ⟩ := h;
    convert h_1_step_applicable_effects prob1 bef1 a ha₁ ha₃ i ha₂ using 1;
    obtain ⟨ k, hk ⟩ := List.mem_iff_getElem.mp ha₁;
    obtain ⟨ hk₁, rfl ⟩ := hk;
    convert h_1_step_applicable_effects prob2 bef2 ( prob2.actions'[k] ) ( by simp [ hlen.symm, hk₁ ] ) _ i _ using 1;
    · unfold applicable' at *; simp_all +decide [ vec_to_state_getElem ] ;
      grind +suggestions;
    · grind;
  · -- Since no action in prob1 adds i, the isSome of h_1_step for prob1 is equal to the isSome of bef1.
    have h_eq_bef1 : ((h_1_step n prob1 bef1)[i]).isSome = (bef1[i]).isSome := by
      rw [ h_1_step_getElem ] ; aesop;
    rw [ h_eq_bef1, show Option.isSome ( h_1_step n prob2 bef2 )[i] = Option.isSome bef2[i] from ?_ ];
    · convert congr_arg ( fun s : State' n => s[i.val] ) hstate using 1 <;> simp +decide [ vec_to_state_getElem ];
    · have h_eq_bef2 : ∀ a ∈ prob2.actions', ¬(i ∈ a.add'.val ∧ applicable' a (vec_to_state n bef2) = true) := by
        intro a ha; contrapose! h; simp_all +decide [ List.mem_iff_getElem ] ;
        obtain ⟨ j, hj, rfl ⟩ := ha; use j; simp_all +decide [ applicable' ] ;
      rw [ h_1_step_getElem ];
      rw [ List.filterMap_eq_nil_iff.mpr ] <;> aesop

/-
The `isSome` pattern of `h_1_iter` after `k` steps depends only on the actions' preconditions
and add-effects (with the same base value vector).
-/
lemma h_1_iter_isSome_eq_of_fields {n : ℕ} (prob1 prob2 : STRIPS n)
    (hlen : prob1.actions'.length = prob2.actions'.length)
    (hpre : ∀ i (h1 : i < prob1.actions'.length) (h2 : i < prob2.actions'.length),
       prob1.actions'[i].pre' = prob2.actions'[i].pre')
    (hadd : ∀ i (h1 : i < prob1.actions'.length) (h2 : i < prob2.actions'.length),
       prob1.actions'[i].add' = prob2.actions'[i].add')
    (base : Vector (WithTop ℕ) n) (k : ℕ) (i : Fin n) :
    ((h_1_iter prob1 base k)[i]).isSome = ((h_1_iter prob2 base k)[i]).isSome := by
  induction' k with k ih generalizing i <;> simp_all +decide [ h_1_iter ];
  convert h_1_step_isSome_eq_of_fields prob1 prob2 hlen ( fun i h1 h2 => hpre i h2 ) ( fun i h1 h2 => hadd i h2 ) ( h_1_iter prob1 base k ) ( h_1_iter prob2 base k ) _ i using 1;
  exact vec_to_state_eq_of_isSome_eq _ _ fun i => ih i

/-- The `isSome` pattern of the `h^max` fixpoint depends only on the actions' preconditions and
add-effects (with the same base value vector). -/
lemma h_1_iter_fix_isSome_eq_of_fields {n : ℕ} (prob1 prob2 : STRIPS n)
    (hlen : prob1.actions'.length = prob2.actions'.length)
    (hpre : ∀ i (h1 : i < prob1.actions'.length) (h2 : i < prob2.actions'.length),
       prob1.actions'[i].pre' = prob2.actions'[i].pre')
    (hadd : ∀ i (h1 : i < prob1.actions'.length) (h2 : i < prob2.actions'.length),
       prob1.actions'[i].add' = prob2.actions'[i].add')
    (base : Vector (WithTop ℕ) n) (i : Fin n)
    (h : ((h_1_iter_fix n prob1 base)[i]).isSome) :
    ((h_1_iter_fix n prob2 base)[i]).isSome := by
  obtain ⟨K1, hK1⟩ := h_1_iter_eventually_fix prob1 base
  apply h_1_iter_fix_isSome_of_iter prob2 base (max K1 0) i
  rw [← h_1_iter_isSome_eq_of_fields prob1 prob2 hlen hpre hadd base (max K1 0) i]
  apply h_1_iter_isSome_mono prob1 base (le_max_left K1 0) i
  rw [hK1]
  exact h
end Validator
