
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
  induction l using List.reverseRecOn <;> aesop

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
def h_1_new {n : ℕ} (prob : STRIPS n) (s : State' n) : ℕ :=
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
When s satisfies g, h_1_new = 0.
-/
lemma h_1_new_goal_aware {n : ℕ} (prob : STRIPS n) (g : VarSet' n) (s : State' n)
    (hsat : satisfies' g s = true) :
    h_1_new (replace_goal prob g) s = 0 := by
  revert @hsat;
  unfold h_1_new;
  simp +decide [ satisfies', replace_goal ];
  intro hsat
  have h_result : ∀ i : Fin n, i ∈ g.val → (h_1_iter_fix n { varNames := prob.varNames, actions' := prob.actions', init' := prob.init', goal' := g } (h_1_base n s))[i] = some 0 := by
                                                              intro i hi
                                                              have h_base : (h_1_base n s)[i] = some 0 := by
                                                                unfold h_1_base; aesop;
                                                              have h_iter : (h_1_iter_fix n { varNames := prob.varNames, actions' := prob.actions', init' := prob.init', goal' := g } (h_1_base n s))[i] ≤ some 0 := by
                                                                                                exact h_1_iter_fix_le n { varNames := prob.varNames, actions' := prob.actions', init' := prob.init', goal' := g } ( h_1_base n s ) i |> le_trans <| h_base.le
                                                              have h_zero : (h_1_iter_fix n { varNames := prob.varNames, actions' := prob.actions', init' := prob.init', goal' := g } (h_1_base n s))[i] = some 0 := by
                                                                                                cases h : ( h_1_iter_fix n { varNames := prob.varNames, actions' := prob.actions', init' := prob.init', goal' := g } ( h_1_base n s ) )[i] <;> simp_all +decide [ WithTop.some_eq_coe ]
                                                              exact h_zero;
  split_ifs <;> simp_all +decide [ vec_to_state ];
  rename_i h;
  obtain ⟨ i, hi, hi' ⟩ := h;
  have h_contra : (h_1_iter_fix n { varNames := prob.varNames, actions' := prob.actions', init' := prob.init', goal' := g } (h_1_base n s))[i].isSome = true := by
                                      grind;
  have h_contra : (vec_to_state n (h_1_iter_fix n { varNames := prob.varNames, actions' := prob.actions', init' := prob.init', goal' := g } (h_1_base n s)))[i.val] = true := by
    convert h_contra using 1
    apply vec_to_state_getElem n _ i
  unfold vec_to_state at h_contra
  aesop

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
  aesop

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

/-- The result vector for h_1_new is the same regardless of the goal. -/
lemma h_1_new_result_eq {n : ℕ} (prob : STRIPS n) (g : VarSet' n) (s : State' n) :
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
    exact List.min_le_of_mem ( List.mem_filterMap.mpr ⟨ a, by aesop ⟩ );
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
For multi-atom goals, h_1_new(g, s) ≤ max of singletons.
-/
set_option maxHeartbeats 400000 in
lemma h_1_new_multi_atom {n : ℕ} (prob : STRIPS n) (g : VarSet' n) (s : State' n)
    (hlen : g.1.length > 1) :
    h_1_new (replace_goal prob g) s ≤
      (g.1.map (fun g' => h_1_new (replace_goal prob ⟨[g'], by simp [List.SortedLT, StrictMono]⟩) s)).max
        (by intro h2; simp_all) := by
  unfold h_1_new;
  simp +decide [ h_1_iter_fix_replace_goal ];
  split_ifs <;> simp_all +decide [ replace_goal ];
  case neg h h_1 =>
    -- Since the goal is satisfied, each singleton goal must also be satisfied.
    have h_singleton_satisfied : ∀ g' ∈ g.val, satisfies' ⟨[g'], by simp [List.SortedLT, StrictMono]⟩ (vec_to_state n (h_1_iter_fix n prob (h_1_base n s))) = true :=
      fun g' a => satisfies'_singleton_of_mem (replace_goal prob g).goal'
                    (vec_to_state n (h_1_iter_fix n prob (h_1_base n s))) g' h a
    simp_all +decide [ List.max ];
    congr! 2;
    refine' List.ext_get _ _ <;> aesop;
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
  grind +suggestions

/-
If g_atom ∈ rg.val and the result vector is the same, then h_1_new(rg, s) ≥ h_1_new([g_atom], s).
-/
lemma h_1_new_mono_of_mem {n : ℕ} (prob : STRIPS n) (g_atom : Fin n) (s : State' n)
    (rg : VarSet' n) (hmem : g_atom ∈ rg.val) :
    h_1_new (replace_goal prob rg) s ≥ h_1_new (replace_goal prob ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩) s := by
  have h_simp : h_1_iter_fix n (replace_goal prob rg) (h_1_base n s) = h_1_iter_fix n prob (h_1_base n s) ∧ h_1_iter_fix n (replace_goal prob ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩) (h_1_base n s) = h_1_iter_fix n prob (h_1_base n s) := by
    exact ⟨ h_1_iter_fix_replace_goal prob rg ( h_1_base n s ), h_1_iter_fix_replace_goal prob ⟨ [ g_atom ], by simp [ List.SortedLT, StrictMono ] ⟩ ( h_1_base n s ) ⟩
  generalize_proofs at *; (
  unfold h_1_new; simp +decide [ h_simp ] ;
  split_ifs <;> simp_all +decide [ replace_goal ];
  · apply List.le_max_of_mem; simp
    exact ⟨ g_atom, hmem, rfl ⟩;
  · simp +decide [ List.max ];
    exact Nat.le_succ_of_le ( Vector.le_maxFinite ( h_1_iter_fix n prob ( h_1_base n s ) |> fun x => x[g_atom] |> fun y => by aesop ) );
  · rename_i h₁ h₂ h₃
    generalize_proofs at *; (
    contrapose! h₃; simp_all +decide [ satisfies' ] ;
    exact h₁ _ hmem))

/-
Case 1: g_atom not discovered at the fixpoint.
-/
lemma h_1_new_singleton_bellman_add_case1 {n : ℕ} (prob : STRIPS n) (g_atom : Fin n) (s : State' n)
    (a : Action n) (ha : a ∈ prob.actions')
    (hadd : g_atom ∈ a.add'.val)
    (hnotSome : (h_1_iter_fix n prob (h_1_base n s))[g_atom] = ⊤) :
    h_1_new (replace_goal prob ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩) s ≤
      a.cost + h_1_new (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩)))) s := by
  -- Since `g_atom` is not discovered at the fixpoint, `h_1_new` returns `Vector.maxFinite result + 1`.
  have h_h1_new_g_atom : h_1_new (replace_goal prob ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩) s = Vector.maxFinite (h_1_iter_fix n prob (h_1_base n s)) + 1 := by
    -- Since `g_atom` is not discovered at the fixpoint, `h_1_new` returns `Vector.maxFinite result + 1` by definition.
    simp [h_1_new]
    split_ifs <;> simp_all
    · simp_all +decide [ replace_goal ]
    · rename_i h₁ h₂;
      erw [ satisfies'_singleton ] at h₁ ; simp_all +decide [ vec_to_state_getElem ];
      exact absurd h₁ ( by erw [ h_1_iter_fix_replace_goal ] ; aesop );
    · rw [ h_1_iter_fix_replace_goal ];
  have h_not_discover_j : ∃ j ∈ a.pre'.val, (h_1_iter_fix n prob (h_1_base n s))[j] = ⊤ := by
    contrapose! hnotSome;
    convert fixpoint_add_applicable_isSome prob ( h_1_iter_fix n prob ( h_1_base n s ) ) ( h_1_iter_fix_is_fixpoint n prob ( h_1_base n s ) ) a ha g_atom hadd _;
    · cases h : ( h_1_iter_fix n prob ( h_1_base n s ) )[g_atom] <;> aesop;
    · exact fun j hj => by specialize hnotSome j hj; cases h : ( h_1_iter_fix n prob ( h_1_base n s ) )[j] <;> aesop;
  obtain ⟨ j, hj₁, hj₂ ⟩ := h_not_discover_j;
  have h_j_in_rg : j ∈ (varset'_of_state' (regress' a (state'_of_varset' ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩))).val := regress_singleton_add_contains_pre a g_atom j hj₁
  have h_h1_new_rg : h_1_new (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩)))) s = Vector.maxFinite (h_1_iter_fix n prob (h_1_base n s)) + 1 := by
    unfold h_1_new;
    simp +decide [ h_1_iter_fix_replace_goal ];
    intro h; have := satisfies'_mem _ _ _ h h_j_in_rg; simp_all +decide [ vec_to_state_getElem ] ;
  linarith

/-
Case 2a: g_atom discovered, action a applicable at fixpoint.
-/
set_option maxHeartbeats 800000 in
lemma h_1_new_singleton_bellman_add_case2a {n : ℕ} (prob : STRIPS n) (g_atom : Fin n) (s : State' n)
    (a : Action n) (ha : a ∈ prob.actions')
    (hadd : g_atom ∈ a.add'.val)
    (hSome : ((h_1_iter_fix n prob (h_1_base n s))[g_atom]).isSome)
    (happ : applicable' a (vec_to_state n (h_1_iter_fix n prob (h_1_base n s))) = true) :
    h_1_new (replace_goal prob ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩) s ≤
      a.cost + h_1_new (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩)))) s := by
  -- Let result = h_1_iter_fix n prob (h_1_base n s).
  set result := h_1_iter_fix n prob (h_1_base n s);
  have h_foldl_le_max : a.pre'.val.attach.foldl (fun acc (x : { x : Fin n // x ∈ a.pre'.val }) => max acc ((result[x.1]).get (vec_to_state_isSome_of_applicable n result a happ x.1 x.2))) 0 ≤ h_1_new (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩)))) s := by
    have h_foldl_le_max : ∀ x ∈ a.pre'.val.attach, ((result[x.1]).get (vec_to_state_isSome_of_applicable n result a happ x.1 x.2)) ≤ h_1_new (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩)))) s := by
      intro x hx
      have h_mem : x.1 ∈ (varset'_of_state' (regress' a (state'_of_varset' ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩))).val := by
        apply regress_singleton_add_contains_pre a g_atom x.1 x.2;
      have := h_1_new_mono_of_mem prob x.1 s (varset'_of_state' (regress' a (state'_of_varset' ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩))) ?_;
      · refine le_trans ?_ this;
        unfold h_1_new;
        simp +decide [ h_1_iter_fix_replace_goal ];
        split_ifs <;> simp_all +decide [ replace_goal ];
        · exact le_rfl;
        · exact Nat.le_succ_of_le ( Vector.le_maxFinite ( h := by aesop ) );
      · exact h_mem;
    have h_foldl_le_max : ∀ {l : List { x : Fin n // x ∈ a.pre'.val }}, (∀ x ∈ l, ((result[x.1]).get (vec_to_state_isSome_of_applicable n result a happ x.1 x.2)) ≤ h_1_new (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩)))) s) → List.foldl (fun acc (x : { x : Fin n // x ∈ a.pre'.val }) => max acc ((result[x.1]).get (vec_to_state_isSome_of_applicable n result a happ x.1 x.2))) 0 l ≤ h_1_new (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩)))) s := by
      intros l hl; induction' l using List.reverseRecOn with l ih <;> aesop;
    exact h_foldl_le_max ‹_›;
  have h_result_le : (result[g_atom]).get hSome ≤ a.cost + a.pre'.val.attach.foldl (fun acc (x : { x : Fin n // x ∈ a.pre'.val }) => max acc ((result[x.1]).get (vec_to_state_isSome_of_applicable n result a happ x.1 x.2))) 0 := by
    apply fixpoint_get_le_action_cost;
    exacts [ h_1_iter_fix_is_fixpoint n prob ( h_1_base n s ), ha, hadd, happ ];
  have h_result_eq : h_1_new (replace_goal prob ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩) s = (result[g_atom]).get hSome := by
    have h_satisfies : satisfies' ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩ (vec_to_state n result) = true := by
      convert vec_to_state_getElem n result g_atom using 1;
      · unfold satisfies'; aesop;
      · exact hSome.symm;
    unfold h_1_new;
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
lemma h_1_new_singleton_bellman_add_case2b {n : ℕ} (prob : STRIPS n) (g_atom : Fin n) (s : State' n)
    (a : Action n)
    (hSome : ((h_1_iter_fix n prob (h_1_base n s))[g_atom]).isSome)
    (hnapp : ¬ applicable' a (vec_to_state n (h_1_iter_fix n prob (h_1_base n s))) = true) :
    h_1_new (replace_goal prob ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩) s ≤
      a.cost + h_1_new (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩)))) s := by
  have h_not_applicable : ∃ j ∈ a.pre'.val, (h_1_iter_fix n prob (h_1_base n s))[j].isSome = false := by
    simp_all +decide [ applicable' ];
    contrapose! hnapp; simp_all +decide [ satisfies', vec_to_state_getElem ] ;
  obtain ⟨ j, hj₁, hj₂ ⟩ := h_not_applicable
  have h_j_in_rg : j ∈ (varset'_of_state' (regress' a (state'_of_varset' ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩))).val := by
    apply regress_singleton_add_contains_pre a g_atom j hj₁;
  have h_h_1_new_rg : h_1_new (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩)))) s = Vector.maxFinite (h_1_iter_fix n prob (h_1_base n s)) + 1 := by
    unfold h_1_new;
    simp +decide [ h_1_iter_fix_replace_goal ];
    intro h; have := satisfies'_mem _ _ _ h h_j_in_rg; simp_all +decide [ vec_to_state_getElem ] ;
  have h_h_1_new_g_atom : h_1_new (replace_goal prob ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩) s = (h_1_iter_fix n prob (h_1_base n s))[g_atom].get hSome := by
    unfold h_1_new;
    simp +decide [ h_1_iter_fix_replace_goal ];
    split_ifs <;> simp_all +decide [ replace_goal ];
    · rfl;
    · unfold satisfies' at *; simp_all +decide [ vec_to_state_getElem ] ;
      grind;
  have h_h_1_new_g_atom_le_maxFinite : (h_1_iter_fix n prob (h_1_base n s))[g_atom].get hSome ≤ Vector.maxFinite (h_1_iter_fix n prob (h_1_base n s)) := by
    apply_rules [ Vector.le_maxFinite ];
    grind;
  linarith

/-- For singleton goals with g_atom ∈ a.add', h_1_new satisfies the bellman bound. -/
lemma h_1_new_singleton_bellman_add {n : ℕ} (prob : STRIPS n) (g_atom : Fin n) (s : State' n)
    (a : Action n) (ha : a ∈ prob.actions')
    (hadd : g_atom ∈ a.add'.val) :
    h_1_new (replace_goal prob ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩) s ≤
      a.cost + h_1_new (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩)))) s := by
  let result := h_1_iter_fix n prob (h_1_base n s)
  cases hcase : result[g_atom] with
  | top => exact h_1_new_singleton_bellman_add_case1 prob g_atom s a ha hadd hcase
  | coe c =>
    have hSome : (result[g_atom]).isSome = true := by rw [hcase]; rfl
    by_cases happ : applicable' a (vec_to_state n result) = true
    · exact h_1_new_singleton_bellman_add_case2a prob g_atom s a ha hadd hSome happ
    · exact h_1_new_singleton_bellman_add_case2b prob g_atom s a hSome happ

/-- For singleton goals, h_1_new satisfies the pointwise bellman bound. -/
lemma h_1_new_singleton_bellman {n : ℕ} (prob : STRIPS n) (g_atom : Fin n) (s : State' n)
    (a : Action n) (ha : a ∈ prob.actions')
    (hreg : regressable' a (state'_of_varset' ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩) = true) :
    h_1_new (replace_goal prob ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩) s ≤
      a.cost + h_1_new (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' ⟨[g_atom], by simp [List.SortedLT, StrictMono]⟩)))) s := by
  by_cases hadd : g_atom ∈ a.add'.val
  · exact h_1_new_singleton_bellman_add prob g_atom s a ha hadd
  · calc h_1_new (replace_goal prob ⟨[g_atom], _⟩) s
        ≤ h_1_new (replace_goal prob (varset'_of_state' (regress' a (state'_of_varset' ⟨[g_atom], _⟩)))) s :=
          h_1_new_mono_of_mem prob g_atom s _ (g_atom_in_regressed_goal_if_not_added a g_atom hadd hreg)
      _ ≤ a.cost + _ := Nat.le_add_left _ _

set_option maxHeartbeats 800000 in
lemma h_1_has_invar {n : ℕ} (prob : STRIPS n):
  h_1_heuristic_regression_invariant prob h_1_new := by
  intro s g
  show _
  split_ifs with hsat hlen
  · exact h_1_new_goal_aware prob g s hsat
  · exact h_1_new_multi_atom prob g s hlen
  · push_neg at hlen
    intro a ha hreg
    rcases g with ⟨l, hl⟩
    cases l with
    | nil => simp [satisfies'] at hsat
    | cons g' t =>
      cases t with
      | nil => exact h_1_new_singleton_bellman prob g' s a ha hreg
      | cons => exfalso; simp [List.length] at hlen

theorem h_1_new_admissible {n : ℕ} (prob : STRIPS n) :
  heur_admissible prob (h_1_new prob) :=
    admissible_of_h_1_regression_invariant prob h_1_new (h_1_has_invar prob) prob.goal'
end Validator
