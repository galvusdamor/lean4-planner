import planning.LMCutH1PCF

/-!
# The i/g normal form preserves `h_1`, and LM-cut dominates `h_1`

This file continues `planning.LMCutH1PCF`.  It is split off so that the (computationally heavy)
`h_1` fixpoint theory it imports is loaded from compiled artifacts.
-/

namespace Validator

set_option maxHeartbeats 1000000

/-
The auxiliary fact `i` (position `n`) of the i/g normal form has `h_1` value `some 0` at every
iteration index: it is true in the initial state, so it starts at `0` and never increases.
-/
lemma ignf_i_fact_iter {n : ℕ} (q : STRIPS n) (k : ℕ) :
    (h_1_iter (i_g_normal_form q) (h_1_base (n + 2) (i_g_normal_form q).init') k)[(⟨n, by omega⟩ : Fin (n + 2))]
      = some 0 := by
  induction' k with k ih generalizing q <;> simp +decide [ *, h_1_iter ] at *
  · unfold h_1_base i_g_normal_form; simp +decide [ STRIPS.init, convertState ] 
  · unfold h_1_step
    convert ih q using 1
    rw [ Vector.getElem_map ]
    simp +decide [ Vector.finRange ]
    intro x hx hx' hx'' hx'''; split_ifs at hx''' <;> simp_all +decide [ updateIfCheaper ] 

/-
Every initial fact of `q` keeps `h_1` value `some 0` along the whole iteration: it starts at `0`
in `h_1_base` and `h_1_step` can only keep it `≤ 0`, i.e. `0`.
-/
lemma q_init_fact_iter {n : ℕ} (q : STRIPS n) (k : ℕ) (g : Fin n) (hg : q.init'[g] = true) :
    (h_1_iter q (h_1_base n q.init') k)[g] = some 0 := by
  induction' k with k ih generalizing q <;> simp +decide [ *, h_1_iter ]
  · unfold h_1_base
    simp_all only [Fin.getElem_fin, Vector.getElem_map, Vector.getElem_finRange, Fin.eta, ↓reduceIte]
  · unfold h_1_step
    rw [ Vector.getElem_map ] ; simp +decide [ hg, ih q hg ]
    unfold updateIfCheaper; simp +decide [ hg, ih q hg ] 

/-- The auxiliary fact `i` (position `n`) has `h_1` *fixpoint* value `some 0`. -/
lemma ignf_fix_i {n : ℕ} (q : STRIPS n) :
    (h_1_iter_fix (n + 2) (i_g_normal_form q)
        (h_1_base (n + 2) (i_g_normal_form q).init'))[(⟨n, by omega⟩ : Fin (n + 2))] = some 0 := by
  obtain ⟨K, hK⟩ := h_1_iter_eventually_fix (i_g_normal_form q)
    (h_1_base (n + 2) (i_g_normal_form q).init')
  rw [← hK]; exact ignf_i_fact_iter q K

/-- q's `h_1` fixpoint vector (the deflation limit from the base of q's initial state). -/
noncomputable def ignf_R0 {n : ℕ} (q : STRIPS n) : _root_.Vector (WithTop ℕ) n :=
  h_1_iter_fix n q (h_1_base n q.init')

/-- The i/g normal form's `h_1` fixpoint vector. -/
noncomputable def ignf_RN {n : ℕ} (q : STRIPS n) : _root_.Vector (WithTop ℕ) (n + 2) :=
  h_1_iter_fix (n + 2) (i_g_normal_form q) (h_1_base (n + 2) (i_g_normal_form q).init')

/-
The only actions of the normal form that add the goal fact `g = ⟨n+1⟩` are (copies of) the
`goal` action: any such action is free and has the embedded goal of `q` as its precondition.
-/
lemma ignf_action_adds_goal {n : ℕ} (q : STRIPS n) (a : Action (n + 2))
    (ha : a ∈ (i_g_normal_form q).actions')
    (hg : (⟨n + 1, by omega⟩ : Fin (n + 2)) ∈ a.add'.val) :
    a.cost = 0 ∧
      a.pre'.val = q.goal'.val.map (Fin.castLE (show n ≤ n + 2 by omega)) := by
  unfold i_g_normal_form at ha; simp_all +decide [ List.mem_append, List.mem_map ] 
  rcases ha with ( ⟨ a, ha, rfl ⟩ | rfl | rfl ) <;> simp_all +decide [ Fin.ext_iff, List.mem_append, List.mem_map ]
  · lia
  · obtain ⟨ a, ha, ha' ⟩ := hg; have := Fin.is_lt a; simp_all +decide [ Fin.ext_iff ] 

/-
q's `h_1` fixpoint value at an initial fact of `q` is `some 0`.
-/
lemma q_fix_init {n : ℕ} (q : STRIPS n) (f : Fin n) (hf : q.init'[f] = true) :
    (ignf_R0 q)[f] = some 0 := by
  have := Validator.h_1_iter_eventually_fix q ( Validator.h_1_base n q.init' )
  convert q_init_fact_iter q this.choose f hf
  exact this.choose_spec.symm

/-
The normal form's `h_1` fixpoint value at an embedded initial fact of `q` is `some 0`
(established at cost 0 by the free `init` action, whose precondition `i` is always `some 0`).
-/
lemma ignf_fix_embed_init {n : ℕ} (q : STRIPS n) (f : Fin n) (hf : q.init'[f] = true) :
    (ignf_RN q)[(Fin.castLE (show n ≤ n + 2 by omega) f)] = some 0 := by
  -- From the definition of `ignf_RN`, we know that it is the fixpoint of the `h_1_step` function for the `i_g_normal_form q`.
  set R := ignf_RN q
  have hR : h_1_step (n + 2) (i_g_normal_form q) R = R := by
    apply Validator.h_1_iter_fix_is_fixpoint
  -- By definition of `i_g_normal_form`, we know that `init` action is in `i_g_normal_form q`'s actions.
  have h_init_action : ∃ a : Action (n + 2), a ∈ (i_g_normal_form q).actions' ∧ a.pre'.val = [⟨n, by omega⟩] ∧ a.add'.val = (varset'_of_state' q.init').val.map (Fin.castLE (show n ≤ n + 2 by omega)) ∧ a.cost = 0 := by
                                                                                                                                                                              unfold i_g_normal_form; simp +decide [ List.mem_append ] 
                                                                                                                                                                              exact ⟨ _, Or.inr <| Or.inl rfl, rfl, rfl, rfl ⟩
  obtain ⟨a, ha₁, ha₂, ha₃, ha₄⟩ := h_init_action
  -- Since `a` is applicable at `R`, we can apply `fixpoint_add_applicable_isSome`.
  have h_applicable : applicable' a (vec_to_state (n + 2) R) = true := by
    unfold applicable'
    have h_i_some : (R[(⟨n, by omega⟩ : Fin (n + 2))]).isSome := by
      have h_i_some : (R[(⟨n, by omega⟩ : Fin (n + 2))]) = some 0 := by
        exact ignf_fix_i q
      grind +splitImp
    grind +suggestions
  have h_le : R[Fin.castLE (show n ≤ n + 2 by omega) f] ≤ some (actionContribUB R a) := by
                              convert fixpoint_value_le_action_cost ( i_g_normal_form q ) R hR a ha₁ ( Fin.castLE ( show n ≤ n + 2 by omega ) f ) _ h_applicable using 1
                              · convert actionContribUB_eq_of_applicable R a h_applicable using 1
                                simp +decide [ ha₂, List.attach ]
                                simp +decide [ List.max ]
                                grind +qlia
                              · simp_all +decide [ varset'_of_state' ]
  have h_actionContribUB : actionContribUB R a = 0 := by
    unfold actionContribUB; simp +decide [ ha₄, ha₂ ] 
    have := ignf_fix_i q; simp_all +decide [ Option.getD ] 
    exact this.symm ▸ rfl
  cases h : R[Fin.castLE (show n ≤ n + 2 by omega) f] <;> simp_all +decide
  cases ‹ℕ› <;> tauto

/-
**Single-step bisimulation at a non-initial embedded fact.** For any value vector `V` of the
normal form whose auxiliary fact `i` has value `some 0`, and any vector `W` of `q` agreeing with `V`
on the embedded facts, the normal form's `h_1_step` at an embedded *non-initial* fact `emb f` equals
q's `h_1_step` at `f`.  (At non-initial facts the free `init` action does not add `emb f`, the `goal`
action adds only `g`, and every embedded action mirrors the corresponding q action since its extra
precondition `i` is `some 0`.)
-/
lemma ignf_step_embed {n : ℕ} (q : STRIPS n) (V : _root_.Vector (WithTop ℕ) (n + 2))
    (W : _root_.Vector (WithTop ℕ) n)
    (hVi : V[(⟨n, by omega⟩ : Fin (n + 2))] = some 0)
    (hWV : ∀ j : Fin n, W[j] = V[(Fin.castLE (show n ≤ n + 2 by omega) j)])
    (f : Fin n) (hf : q.init'[f] = false) :
    (h_1_step (n + 2) (i_g_normal_form q) V)[(Fin.castLE (show n ≤ n + 2 by omega) f)]
      = (h_1_step n q W)[f] := by
  -- Since $V$ and $W$ agree on $f$, the lists of actions contributing to the h_1_step are the same.
  have h_lists_eq : (i_g_normal_form q).actions'.filterMap (fun a => if Fin.castLE (by omega) f ∈ a.add'.val then if applicable' a (vec_to_state (n + 2) V) then some (actionContribUB V a) else none else none) = q.actions'.filterMap (fun a => if f ∈ a.add'.val then if applicable' a (vec_to_state n W) then some (actionContribUB W a) else none else none) := by
    unfold i_g_normal_form
    simp +decide [ List.filterMap_append, List.filterMap_map ]
    rw [ List.filterMap_cons, List.filterMap_cons ] ; simp +decide [ Fin.ext_iff, Fin.val_add ]
    rw [ if_neg, if_neg ] <;> norm_num [ Fin.ext_iff, Fin.val_add ]
    · refine' List.filterMap_congr _
      intro a ha; simp +decide [ Fin.castLE_injective, List.mem_map, List.mem_append, List.mem_singleton ] 
      congr! 2
      · unfold applicable'
        unfold satisfies'; simp +decide [ Fin.castLE_injective, List.mem_map, List.mem_append, List.mem_singleton ] 
        grind +suggestions
      · unfold actionContribUB; simp +decide [ hWV ] 
        unfold Option.getD
        simp_all only [Fin.getElem_fin, Fin.val_castLE, zero_le, sup_of_le_left]
        rfl
    · linarith [ Fin.is_lt f ]
    · intro x hx; intro H; have := varset'_of_state'_mem q.init' x; simp_all +decide [ Fin.ext_iff ] 
  grind +suggestions

/-- The extension of q's `h_1` fixpoint vector to the normal form: embedded facts get q's value,
the auxiliary `i` gets `some 0`, and the goal `g` gets the goal-action contribution. -/
noncomputable def ignf_extend {n : ℕ} (q : STRIPS n) : _root_.Vector (WithTop ℕ) (n + 2) :=
  _root_.Vector.ofFn (fun idx : Fin (n + 2) =>
    if h : idx.val < n then (ignf_R0 q)[(⟨idx.val, h⟩ : Fin n)]
    else if idx.val = n then some 0
    else if q.goal'.val.all (fun f => ((ignf_R0 q)[f]).isSome) then
      some ((q.goal'.val.map (fun f => ((ignf_R0 q)[f]).getD 0)).foldl max 0)
    else none)

/-
`ignf_extend` value at an embedded fact.
-/
lemma ignf_extend_emb {n : ℕ} (q : STRIPS n) (f : Fin n) :
    (ignf_extend q)[(Fin.castLE (show n ≤ n + 2 by omega) f)] = (ignf_R0 q)[f] := by
  grind +locals

/-
`ignf_extend` value at the auxiliary fact `i`.
-/
lemma ignf_extend_i {n : ℕ} (q : STRIPS n) :
    (ignf_extend q)[(⟨n, by omega⟩ : Fin (n + 2))] = some 0 := by
  unfold ignf_extend
  simp_all only [Fin.getElem_fin, List.all_eq_true, Vector.getElem_ofFn, lt_self_iff_false,
    ↓reduceDIte, ↓reduceIte]

/-
`h_1_step` of the normal form fixes `ignf_extend` at the embedded facts.
-/
lemma ignf_extend_step_emb {n : ℕ} (q : STRIPS n) (f : Fin n) :
    (h_1_step (n + 2) (i_g_normal_form q) (ignf_extend q))[(Fin.castLE (show n ≤ n + 2 by omega) f)]
      = (ignf_extend q)[(Fin.castLE (show n ≤ n + 2 by omega) f)] := by
  by_cases hf : q.init'[f] = false
  · convert ignf_step_embed q ( ignf_extend q ) ( ignf_R0 q ) ( ignf_extend_i q ) ( fun j => ( ignf_extend_emb q j ).symm ) f hf using 1
    rw [ show h_1_step n q ( ignf_R0 q ) = ignf_R0 q from ?_ ]
    · grind +locals
    · convert h_1_iter_fix_is_fixpoint n q ( h_1_base n q.init' ) using 1
  · have h_eq : (h_1_step (n + 2) (i_g_normal_form q) (ignf_extend q))[(Fin.castLE (show n ≤ n + 2 by omega) f)] ≤ (ignf_extend q)[(Fin.castLE (show n ≤ n + 2 by omega) f)] := by
                                                                                                                                                  apply h_1_step_le
    have h_eq : (ignf_extend q)[(Fin.castLE (show n ≤ n + 2 by omega) f)] = some 0 := by
                                              convert q_fix_init q f ( by simpa using hf ) using 1
                                              exact ignf_extend_emb q f
    cases h : ( h_1_step ( n + 2 ) ( i_g_normal_form q ) ( ignf_extend q ) )[ Fin.castLE ( show n ≤ n + 2 by omega ) f ] <;> simp_all +decide
    cases ‹ℕ› <;> tauto

/-
`h_1_step` of the normal form fixes `ignf_extend` at the auxiliary fact `i`.
-/
lemma ignf_extend_step_i {n : ℕ} (q : STRIPS n) :
    (h_1_step (n + 2) (i_g_normal_form q) (ignf_extend q))[(⟨n, by omega⟩ : Fin (n + 2))]
      = (ignf_extend q)[(⟨n, by omega⟩ : Fin (n + 2))] := by
  convert h_1_step_getElem_contrib ( i_g_normal_form q ) ( ignf_extend q ) ( ⟨ n, by omega ⟩ : Fin ( n + 2 ) ) using 1
  unfold i_g_normal_form; simp +decide [ List.mem_append, List.mem_map ] 
  grind

/-
`h_1_step` of the normal form fixes `ignf_extend` at the goal fact `g`.
-/
lemma ignf_extend_step_g {n : ℕ} (q : STRIPS n) :
    (h_1_step (n + 2) (i_g_normal_form q) (ignf_extend q))[(⟨n + 1, by omega⟩ : Fin (n + 2))]
      = (ignf_extend q)[(⟨n + 1, by omega⟩ : Fin (n + 2))] := by
  rw [ h_1_step_getElem_contrib ] ; simp +decide [ i_g_normal_form ] 
  unfold updateIfCheaper; simp +decide [ Fin.ext_iff ] 
  rw [ show ( ignf_extend q)[n + 1] = if q.goal'.val.all ( fun f => ( ignf_R0 q)[f].isSome ) then some ( ( q.goal'.val.map ( fun f => ( ignf_R0 q)[f].getD 0 ) ).foldl max 0 ) else none from ?_ ] ; split_ifs <;> simp +decide [ * ] at *
  · simp +decide [ List.filterMap, List.map ] at *
    split_ifs <;> simp +decide [ Fin.ext_iff ] at *
    rename_i h₁ h₂ h₃ h₄
    obtain ⟨ a, ha₁, ha₂ ⟩ := h₂; simp_all +decide [ Fin.ext_iff ] 
    exact absurd ha₂ ( by exact ne_of_lt ( Nat.lt_succ_of_le ( Nat.le_of_lt_succ ( by simp +decide [ Fin.ext_iff ] ) ) ) )
    · grind
    · rename_i h₁ h₂ h₃ h₄
      obtain ⟨ a, ha₁, ha₂ ⟩ := h₂; simp_all +decide [ Fin.ext_iff ] 
      exact absurd ha₂ ( by exact ne_of_lt ( Nat.lt_succ_of_le ( Nat.le_of_lt_succ ( by simp +decide [ Fin.ext_iff ] ) ) ) )
    · grind +qlia
    · intro h₁ h₂
      contrapose! h₂
      rw [ List.min_eq_head ]
      · simp +decide [ actionContribUB ]
        rw [ List.head_append ] ; simp +decide [ Fin.ext_iff ]
        split_ifs <;> simp_all +decide [ Fin.ext_iff ]
        · congr! 2
          ext f; simp +decide [ ignf_extend_emb ] 
          convert ignf_extend_emb q f |> Eq.symm using 1
          grind +suggestions
        · grind
      · simp +decide [ List.pairwise_append, List.pairwise_cons ]
        constructor
        · rw [ List.filterMap_eq_nil_iff.mpr ] <;> simp +decide [ List.Pairwise ]
          intro a ha x hx hx'; simp_all +decide [ Fin.ext_iff ] 
          bv_omega
        · intro a x hx y hy hxy h₁ h₂; subst h₂; simp_all +decide [ Fin.ext_iff ] 
          bv_omega
    · grind +splitIndPred
  · refine' ⟨ _, _, _ ⟩
    · grind +suggestions
    · grind +splitImp
    · unfold applicable'; simp +decide [ vec_to_state_getElem ] 
      unfold satisfies'; simp +decide [ vec_to_state_getElem ] 
      unfold ignf_extend
      simp_all only [Fin.getElem_fin, List.all_eq_true, Vector.getElem_ofFn, Fin.is_lt, ↓reduceDIte]
  · unfold ignf_extend; simp +decide [ Fin.ext_iff ] 

/-
`ignf_extend` is an `h_1_step`-fixpoint of the normal form.
-/
lemma ignf_extend_fixpoint {n : ℕ} (q : STRIPS n) :
    h_1_step (n + 2) (i_g_normal_form q) (ignf_extend q) = ignf_extend q := by
  -- By definition of `ignf_extend`, we know that it is a fixpoint of `h_1_step`.
  apply Vector.ext
  intro i hi
  by_cases hi' : i = n ∨ i = n + 1
  · cases hi' <;> simp_all +decide [ Fin.ext_iff ]
    · convert ignf_extend_step_i q using 1
    · convert ignf_extend_step_g q using 1
  · convert ignf_extend_step_emb q ⟨ i, by omega ⟩ using 1

/-
**Embedded-fact agreement.** The normal form's `h_1` fixpoint at an embedded original fact
equals q's `h_1` fixpoint there.  This is the crux of `h_1_i_g_normal_form_eq`, proved by two-sided
deflation domination (`h_1_iter_fix_ge_of_fixpoint`, `h_1_step_mono`): the embedded actions of the
normal form (each carrying the always-`some 0` auxiliary precondition `i`) mirror q's actions, and
the free `init` action establishes exactly the embedded initial facts at cost 0.
-/
lemma ignf_fix_embed {n : ℕ} (q : STRIPS n) (f : Fin n) :
    (ignf_RN q)[(Fin.castLE (show n ≤ n + 2 by omega) f)] = (ignf_R0 q)[f] := by
  apply le_antisymm
  · set W : _root_.Vector (WithTop ℕ) n := _root_.Vector.ofFn (fun j : Fin n => (ignf_RN q)[(Fin.castLE (show n ≤ n + 2 by omega) j)])
    have hW_fixpoint : h_1_step n q W = W := by
      have hW_fixpoint : ∀ f' : Fin n, (h_1_step n q W)[f'] = W[f'] := by
        intro f'
        by_cases hf' : q.init'[f'] = true
        · have hW_f' : W[f'] = some 0 := by
            have := ignf_fix_embed_init q f' hf'
            simp_all only [Fin.getElem_fin, Fin.val_castLE, Vector.getElem_ofFn,
              W]
          have hW_f'_step : (h_1_step n q W)[f'] ≤ W[f'] := by
            apply h_1_step_le
          cases h : ( h_1_step n q W)[f'] <;> simp_all +decide
          exact le_antisymm hW_f'_step ( WithTop.coe_le_coe.mpr ( Nat.zero_le _ ) )
        · have := ignf_step_embed q (ignf_RN q) W (ignf_fix_i q) (fun j => by simp [W]) f' (by simpa using hf')
          rw [ ← this, show ( h_1_step ( n + 2 ) ( i_g_normal_form q ) ( ignf_RN q ) ) = ignf_RN q from h_1_iter_fix_is_fixpoint _ _ _ ]
          simp [W]
      ext i; exact (by
      convert hW_fixpoint ⟨ i, by linarith ⟩)
    convert h_1_iter_fix_ge_of_fixpoint q ( h_1_base n q.init' ) W hW_fixpoint ( fun j => ?_ ) f using 1
    · simp_all only [Fin.getElem_fin, Fin.val_castLE, Vector.getElem_ofFn, W]
    · by_cases hj : q.init'[j] = true <;> simp_all +decide [ h_1_base ]
      · have := ignf_fix_embed_init q j hj
        simp_all only [Fin.getElem_fin, Fin.val_castLE, Vector.getElem_ofFn,
          le_refl, W]
      · exact le_top
  · convert h_1_iter_fix_ge_of_fixpoint ( i_g_normal_form q ) ( h_1_base ( n + 2 ) ( i_g_normal_form q ).init' ) ( ignf_extend q ) _ _ ( Fin.castLE ( show n ≤ n + 2 by omega ) f ) using 1
    · rw [ ignf_extend_emb ]
    · exact ignf_extend_fixpoint q
    · intro i; unfold ignf_extend; simp +decide [ h_1_base ] 
      split_ifs <;> simp_all +decide [ i_g_normal_form ]
      · linarith
      · exact le_top
      · exact le_top

/-
In the satisfied case, `h_1 q q.init'` is bounded by the maximal finite fixpoint value
(it is a max over goal facts of their fixpoint values, each `≤ maxFinite`).
-/
lemma h_1_le_maxFinite_of_satisfies {n : ℕ} (q : STRIPS n)
    (h : satisfies' q.goal' (vec_to_state n (ignf_R0 q)) = true) :
    h_1 q q.init' ≤ Vector.maxFinite (ignf_R0 q) := by
  simp_all +decide [ h_1 ]
  split_ifs
  · exact Nat.zero_le _
  · have h_max_le : ∀ x ∈ (q.goal'.val.attach.map (fun x => (ignf_R0 q)[x.1].get (vec_to_state_isSome_of_satisfies n (ignf_R0 q) q.goal' h x.1 x.2))), x ≤ Vector.maxFinite (ignf_R0 q) := by
      intros x hx
      obtain ⟨ y, hy, rfl ⟩ := List.mem_map.mp hx
      apply Vector.le_maxFinite
      rw [ Option.some_get ]
    exact (List.max_le_iff _).mpr h_max_le
  · contradiction

/-
The goal fact `g` (position `n+1`) of the normal form is reached (its fixpoint value is `some`)
iff the goal of `q` is satisfied at q's fixpoint.
-/
lemma ignf_fix_goal_isSome {n : ℕ} (q : STRIPS n) :
    ((ignf_RN q)[(⟨n + 1, by omega⟩ : Fin (n + 2))]).isSome
      = satisfies' q.goal' (vec_to_state n (ignf_R0 q)) := by
  by_contra h_contra
  by_cases h : satisfies' q.goal' (vec_to_state n (ignf_R0 q)) <;> simp_all +decide
  · obtain ⟨a, ha⟩ : ∃ a : Action (n + 2), a ∈ (i_g_normal_form q).actions' ∧ a.pre'.val = q.goal'.val.map (Fin.castLE (show n ≤ n + 2 by omega)) ∧ (⟨n + 1, by omega⟩ : Fin (n + 2)) ∈ a.add'.val := by
                                                                                                                          unfold i_g_normal_form; simp +decide [ List.mem_append ] 
                                                                                                                          exact ⟨ _, Or.inr <| Or.inr rfl, rfl, by simp +decide ⟩
    have h_precondition_some : ∀ f ∈ a.pre'.val, (ignf_RN q)[f].isSome := by
      grind +suggestions
    have := fixpoint_add_applicable_isSome (i_g_normal_form q) (ignf_RN q) (h_1_iter_fix_is_fixpoint (n + 2) (i_g_normal_form q) (h_1_base (n + 2) (i_g_normal_form q).init')) a ha.1 (⟨n + 1, by omega⟩ : Fin (n + 2)) ha.2.2 h_precondition_some
    simp_all only [List.mem_map,
      Fin.getElem_fin, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Fin.val_castLE, Option.isSome_none,
      Bool.false_eq_true]
  · obtain ⟨a, ha, hadd, happ⟩ : ∃ a ∈ (i_g_normal_form q).actions', applicable' a (vec_to_state (n + 2) (ignf_RN q)) = true ∧ (⟨n + 1, by omega⟩ : Fin (n + 2)) ∈ a.add'.val := by
      have := fixpoint_get_attained ( i_g_normal_form q ) ( i_g_normal_form q ).init' ⟨ n + 1, by omega ⟩ ?_ ?_
      · exact ⟨ this.choose, this.choose_spec.1, this.choose_spec.2.2.1, this.choose_spec.2.1 ⟩
      · exact Option.isSome_iff_ne_none.mpr h_contra
      · unfold i_g_normal_form; simp +decide [ Vector.getElem_push ] 
    obtain ⟨hcost, hpre⟩ := ignf_action_adds_goal q a ha happ
    have h_pre_some : ∀ f ∈ q.goal'.val, (ignf_RN q)[(Fin.castLE (show n ≤ n + 2 by omega) f)].isSome := by
                                                                    intros f hf
                                                                    apply vec_to_state_isSome_of_applicable
                                                                    exact hadd
                                                                    simp_all only [List.mem_map, Fin.castLE_inj,
                                                                      exists_eq_right]
    grind +suggestions

/-
In the satisfied case, the `foldl max 0` over the goal facts of q's fixpoint values equals
`h_1 q q.init'` (the goal-action contribution coincides with the `h_1` goal read-off).
-/
lemma ignf_goal_foldl_eq {n : ℕ} (q : STRIPS n)
    (h : satisfies' q.goal' (vec_to_state n (ignf_R0 q)) = true) :
    (q.goal'.val.map (fun f => ((ignf_R0 q)[f]).getD 0)).foldl max 0 = h_1 q q.init' := by
  unfold h_1
  by_cases h : q.goal'.val = [] <;> simp_all +decide
  · convert ‹satisfies' q.goal' ( vec_to_state n ( ignf_R0 q ) ) = true› using 1
  · have h_foldl_max : ∀ (l : List ℕ) (hl : l ≠ []), List.foldl max 0 l = List.max l hl := by
      intros l hl; induction' l using List.reverseRecOn with l ih <;> simp_all +decide [ List.max ] 
      · contradiction
      · cases l <;> simp_all +decide [ List.foldl ]
    convert h_foldl_max _ _ using 2
    all_goals simp_all +decide [ List.map ]
    split_ifs ; simp_all +decide [ ignf_R0 ]
    · convert rfl
      refine' List.ext_get _ _ <;> simp +decide [ List.get ]
      intro i hi₁ hi₂; rw [ Option.getD_eq_iff ] ; simp +decide [ hi₁, hi₂ ] 
    · contradiction

/-
When q's goal is satisfied, the normal form's fixpoint goal-value equals `h_1 q q.init'`.
-/
lemma ignf_fix_goal_value {n : ℕ} (q : STRIPS n)
    (h : satisfies' q.goal' (vec_to_state n (ignf_R0 q)) = true) :
    (ignf_RN q)[(⟨n + 1, by omega⟩ : Fin (n + 2))] = some (h_1 q q.init') := by
  have := ignf_fix_goal_isSome q
  have := fixpoint_get_attained ( i_g_normal_form q ) ( i_g_normal_form q ).init' ⟨ n + 1, by omega ⟩ ; simp_all +decide [ ignf_action_adds_goal ] 
  obtain ⟨ a, ha₁, ha₂, ha₃, ha₄ ⟩ := this ‹_› ( by
    simp +decide [ i_g_normal_form ] )
  obtain ⟨ ha₅, ha₆ ⟩ := ignf_action_adds_goal q a ha₁ ha₃
  have ha₇ : actionContribUB (ignf_RN q) a = (q.goal'.val.map (fun f => ((ignf_R0 q)[f]).getD 0)).foldl max 0 := by
    unfold actionContribUB; simp +decide [ ha₅, ha₆ ] 
    exact congr_arg _ ( List.map_congr_left fun x hx => by have := ignf_fix_embed q x; simp_all only [Fin.getElem_fin, Fin.val_castLE, Function.comp_apply] )
  have ha₈ : (q.goal'.val.map (fun f => ((ignf_R0 q)[f]).getD 0)).foldl max 0 = h_1 q q.init' := by
    exact ignf_goal_foldl_eq q h
  cases h : ( ignf_RN q)[n + 1] <;> simp_all +decide [ ignf_RN ]
  exact ha₄ ▸ rfl

/-
A uniform upper bound on all finite entries bounds `Vector.maxFinite`.
-/
lemma maxFinite_le {m : ℕ} (v : _root_.Vector (WithTop ℕ) m) (B : ℕ)
    (h : ∀ i : Fin m, ∀ c : ℕ, v[i] = some c → c ≤ B) : Vector.maxFinite v ≤ B := by
  induction v using Vector.recOn ; simp_all +decide [ Vector.maxFinite ]
  have h_foldl_le_B : ∀ (l : List (WithTop ℕ)), (∀ x ∈ l, ∀ c, x = some c → c ≤ B) → List.foldl (fun acc x => match x with | some c => max acc c | none => acc) 0 l ≤ B := by
    intro l hl
    induction' l using List.reverseRecOn with l ih
    · exact Nat.zero_le _
    · grind +extAll
  convert h_foldl_le_B ( List.map ( fun i : Fin m => ‹Array ( WithTop ℕ ) ›[i] ) ( List.finRange m ) ) _ using 1
  · rw [ ← List.foldl_toArray ]
    congr
    · grind +qlia
    · simp +decide [ * ]
  · grind

/-
The maximal finite fixpoint value is preserved by the normal form (the auxiliary `i = some 0`
and goal `g` facts do not increase it, and the embedded facts carry exactly q's values).
-/
lemma ignf_maxFinite_eq {n : ℕ} (q : STRIPS n) :
    Vector.maxFinite (ignf_RN q) = Vector.maxFinite (ignf_R0 q) := by
  -- Let `R := ignf_RN q`, `R0 := ignf_R0 q`, `emb := Fin.castLE (n ≤ n+2)`.
  set R := ignf_RN q
  set R0 := ignf_R0 q
  set emb : Fin n → Fin (n + 2) := Fin.castLE (show n ≤ n + 2 by omega)
  refine' le_antisymm ( maxFinite_le _ _ _ ) ( maxFinite_le _ _ _ )
  · -- Let `idx : Fin (n + 2)`, `c` with `R[idx] = some c`.
    intro idx c hc
    by_cases hidx : idx.val < n
    · -- Since `idx.val < n`, we have `idx = emb ⟨idx.val, hidx⟩`.
      have hidx_eq : idx = emb ⟨idx.val, hidx⟩ := Fin.eq_of_val_eq rfl
      rw [ hidx_eq ] at hc
      rw [ ignf_fix_embed ] at hc
      exact Vector.le_maxFinite hc
    · by_cases hidx' : idx.val = n
      · have := ignf_fix_i q; simp_all +decide [ Fin.ext_iff ] 
        cases this.symm.trans hc
        simp_all only [zero_le, R, R0]
      · -- Since `idx.val = n + 1`, we have `R[idx] = some c` implies `satisfies' q.goal' (vec_to_state n R0)`.
        have h_satisfies : satisfies' q.goal' (vec_to_state n R0) := by
          have h_satisfies : idx = ⟨n + 1, by omega⟩ := by
            grind
          have := ignf_fix_goal_isSome q
          simp_all only [Fin.getElem_fin, add_lt_iff_neg_left, not_lt_zero,
            not_false_eq_true, Nat.add_eq_left, one_ne_zero, Option.isSome_some, Bool.true_eq, R, R0]
        have h_c_eq_h1 : c = h_1 q q.init' := by
          have h_c_eq_h1 : R[(⟨n + 1, by omega⟩ : Fin (n + 2))] = some (h_1 q q.init') := by
            exact ignf_fix_goal_value q h_satisfies
          grind
        exact h_c_eq_h1.symm ▸ h_1_le_maxFinite_of_satisfies q h_satisfies
  · intro i c hc
    have h_emb : R[emb i] = some c := by
      rw [ ← hc, ignf_fix_embed ]
    exact Vector.le_maxFinite h_emb

/-
**The i/g normal form preserves `h_1`.** The `h_1` value of the i/g normal form (evaluated at its
own initial state, against its single goal fact `g`) equals the `h_1` value of the original problem.
This is the `h_1`/`h^max` analogue of `i_g_normal_form_keeps_h_plus`.

The route is a fixpoint embedding `(h_1_iter_fix … (i_g_normal_form q) …)[Fin.castLE _ f] =
(h_1_iter_fix … q …)[f]` (`ignf_fix_embed`), the goal read-off (`ignf_fix_goal_isSome`,
`ignf_fix_goal_value`), the auxiliary fact value (`ignf_fix_i`), and the `maxFinite` invariance
(`ignf_maxFinite_eq`).
-/
lemma h_1_i_g_normal_form_eq {n : ℕ} (q : STRIPS n) :
    h_1 (i_g_normal_form q) (i_g_normal_form q).init' = h_1 q q.init' := by
  by_contra h_contra
  revert h_contra
  intro h
  -- By definition of `h_1`, we know that `h_1 (i_g_normal_form q) (i_g_normal_form q).init'` is equal to `Vector.maxFinite (ignf_RN q) + 1` if the goal is not satisfied, and `pre_cost.max` otherwise.
  have h_def : h_1 (i_g_normal_form q) (i_g_normal_form q).init' = if (ignf_RN q)[(⟨n + 1, by omega⟩ : Fin (n + 2))].isSome then (ignf_RN q)[(⟨n + 1, by omega⟩ : Fin (n + 2))].get! else Vector.maxFinite (ignf_RN q) + 1 := by
    unfold h_1
    unfold ignf_RN; simp +decide [ satisfies'_singleton, vec_to_state_getElem ] 
    split_ifs <;> simp_all +decide [ Option.isSome_iff_exists ]
    · unfold i_g_normal_form at *
      simp_all only [BitVec.zero_eq, BitVec.zero_or, List.cons_ne_self]
    · rename_i h₁ h₂ h₃; specialize h₃ 0; simp_all +decide [ i_g_normal_form ] 
    · unfold i_g_normal_form; simp +decide [ satisfies'_singleton, vec_to_state_getElem ] 
      grind +suggestions
    · unfold i_g_normal_form at *; simp_all +decide [ satisfies'_singleton, vec_to_state_getElem ] 
      grind +suggestions
    · rename_i h₁ h₂; obtain ⟨ a, ha ⟩ := h₂; simp_all +decide [ satisfies'_singleton, vec_to_state_getElem ] 
      unfold satisfies' at h₁; simp_all +decide [ vec_to_state_getElem ] 
      unfold i_g_normal_form at h₁; simp_all +decide [ List.SortedLT, StrictMono ] 
      unfold i_g_normal_form at ha; simp_all +decide [ List.SortedLT, StrictMono ] 
  split_ifs at h_def <;> simp_all +decide [ ignf_maxFinite_eq ]
  · have := ignf_fix_goal_value q ( by
      exact ignf_fix_goal_isSome q |> fun h => h.symm.trans ‹_› )
    exact h ( by erw [ this ] ; rfl )
  · unfold h_1 at h
    have := ignf_fix_goal_isSome q; simp_all +decide [ ignf_RN, ignf_R0 ] 

/-
**(B)** The `h_1`/`h^max` value of the goal fact of the i/g normal form (from its initial state)
equals the original `h_1` value of `prob` at `s`.
-/
lemma h1_goal_value_normal_form {n : ℕ} (prob : STRIPS n) (s : State' n)
    (hg : prob.goal'.val ≠ []) :
    h1_goal_value (i_g_normal_form (set_init prob s))
        (get_unitary_goal (i_g_normal_form (set_init prob s))
          (i_g_normalform_is_unitary_goal _))
      = h_1 prob s := by
  convert h_1_i_g_normal_form_eq ( set_init prob s ) using 1
  exact h_1_set_init prob s s ▸ rfl

/-
If the goal is empty it is trivially satisfied, so `h_1` returns `0`.
-/
lemma h_1_of_empty_goal {n : ℕ} (prob : STRIPS n) (s : State' n) (hg : prob.goal'.val = []) :
    h_1 prob s = 0 := by
  -- Unfold `h_1` and simplify using the empty goal condition `hg`, which makes the initial `if hg : prob.goal'.val = [] then ...` reduce to `0`.
  -- This avoids needing any further reasoning about the fixpoint `h_1_iter_fix`.
  unfold h_1
  simp [hg]
  unfold satisfies'
  simp_all only [Fin.getElem_fin, List.all_nil]

/-- **LM-cut with the `h_1`-maximiser pcf dominates `h_1`.**

For every solvable state `s` (witnessed by a plan), the LM-cut heuristic value computed with the
`h_1`-maximiser precondition-choice function is at least the `h_1` heuristic value. -/
theorem lmcut_h1_dominates {n : ℕ} (prob : STRIPS n) (s : State' n)
    (plan : Plan prob (convertState s)) :
    lmcut prob s (@h1_pcf n) ≥ h_1 prob s := by
  rw [lmcut]
  split
  · -- empty goal: `h_1 prob s = 0`
    rename_i hg
    exact (h_1_of_empty_goal prob s hg).le
  · rename_i hg
    -- lift the plan to a plan of the i/g normal form of `set_init prob s`
    obtain ⟨p', hp'⟩ := path_set_init_transfer prob s plan.path
    obtain ⟨eplan, _⟩ := ignf_plan_lift (set_init prob s) ⟨plan.last, p', plan.goal⟩
    have hcore := lmcut_inner_ge_h1_goal _ (i_g_normal_form (set_init prob s))
      (i_g_normalform_is_unitary_init _) (i_g_normalform_is_unitary_goal _)
      (i_g_normal_form_has_preconditions (set_init prob s) hg) rfl eplan
    rw [h1_goal_value_normal_form prob s hg] at hcore
    exact hcore

end Validator