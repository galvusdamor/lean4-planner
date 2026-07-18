import planning.LMCutH1PCF

/-!
# The i/g normal form preserves `h_1`, and LM-cut dominates `h_1`

This file continues `planning.LMCutH1PCF`.  It is split off so that the (computationally heavy)
`h_1` fixpoint theory it imports is loaded from compiled artifacts.
-/

namespace STRIPS

set_option maxHeartbeats 1000000

/-
The auxiliary fact `i` (position `n`) of the i/g normal form has `h_1` value `some 0` at every
iteration index: it is true in the initial state, so it starts at `0` and never increases.
-/
lemma ignf_i_fact_iter {n : ℕ} (q : PlanningTask n) (k : ℕ) :
    (h_1_iter (i_g_normal_form q) (h_1_base (n + 2) (i_g_normal_form q).init') k)[(⟨n, by omega⟩ : Fin (n + 2))]
      = some 0 := by
  induction' k with k ih generalizing q <;> simp [ *, h_1_iter ] at *
  · unfold h_1_base i_g_normal_form; simp
  · unfold h_1_step
    convert ih q using 1
    rw [ Vector.getElem_map ]
    simp [ Vector.finRange ]
    intro x hx hx' hx'' hx'''; split_ifs at hx''' <;> simp_all [ updateIfCheaper ]

/-
Every initial fact of `q` keeps `h_1` value `some 0` along the whole iteration: it starts at `0`
in `h_1_base` and `h_1_step` can only keep it `≤ 0`, i.e. `0`.
-/
lemma q_init_fact_iter {n : ℕ} (q : PlanningTask n) (k : ℕ) (g : Fin n) (hg : q.init'[g] = true) :
    (h_1_iter q (h_1_base n q.init') k)[g] = some 0 := by
      induction' k with k ih;
      · unfold h_1_iter h_1_base; aesop;
      · refine' le_antisymm _ _ <;> simp_all +decide [ h_1_iter ];
        · refine' le_trans ( h_1_step_le _ _ _ _ ) _;
          exact ih.le;
        · finiteness

lemma ignf_fix_i {n : ℕ} (q : PlanningTask n) :
    (h_1_iter_fix (n + 2) (i_g_normal_form q)
        (h_1_base (n + 2) (i_g_normal_form q).init'))[(⟨n, by omega⟩ : Fin (n + 2))] = some 0 := by
  obtain ⟨K, hK⟩ := h_1_iter_eventually_fix (i_g_normal_form q)
    (h_1_base (n + 2) (i_g_normal_form q).init')
  rw [← hK]; exact ignf_i_fact_iter q K

/-- q's `h_1` fixpoint vector (the deflation limit from the base of q's initial state). -/
noncomputable def ignf_R0 {n : ℕ} (q : PlanningTask n) : _root_.Vector (WithTop ℕ) n :=
  h_1_iter_fix n q (h_1_base n q.init')

/-- The i/g normal form's `h_1` fixpoint vector. -/
noncomputable def ignf_RN {n : ℕ} (q : PlanningTask n) : _root_.Vector (WithTop ℕ) (n + 2) :=
  h_1_iter_fix (n + 2) (i_g_normal_form q) (h_1_base (n + 2) (i_g_normal_form q).init')

/-
The only actions of the normal form that add the goal fact `g = ⟨n+1⟩` are (copies of) the
`goal` action: any such action is free and has the embedded goal of `q` as its precondition.
-/
lemma ignf_action_adds_goal {n : ℕ} (q : PlanningTask n) (a : Action (n + 2))
    (ha : a ∈ (i_g_normal_form q).actions')
    (hg : (⟨n + 1, by omega⟩ : Fin (n + 2)) ∈ a.add'.toList) :
    a.cost = 0 ∧
      a.pre'.toList = q.goal'.toList.map (Fin.castLE (show n ≤ n + 2 by omega)) := by
  unfold i_g_normal_form at ha; simp_all +decide [ Finset.ext_iff,PlanningTask ] ;
  rcases ha with ( ⟨ b, hb, rfl ⟩ | rfl | rfl ) <;> simp_all +decide [ toVarSet' ];
  · obtain ⟨ a, ha, ha' ⟩ := hg; have := Fin.is_lt a; simp_all +decide [ Fin.ext_iff ] ;
  · obtain ⟨ a, ha, ha' ⟩ := hg; have := Fin.is_lt a; simp_all +decide [ Fin.ext_iff ] ;
  · unfold VarSet'.toList; simp +decide [ Finset.sort ] ;
    rw [ List.mergeSort_eq_self ];
    · grind +suggestions;
    · rw [ List.pairwise_iff_get ];
      grind +suggestions

lemma q_fix_init {n : ℕ} (q : PlanningTask n) (f : Fin n) (hf : q.init'[f] = true) :
    (ignf_R0 q)[f] = some 0 := by
  have := STRIPS.h_1_iter_eventually_fix q ( STRIPS.h_1_base n q.init' )
  convert q_init_fact_iter q this.choose f hf
  exact this.choose_spec.symm

/-
The normal form's `h_1` fixpoint value at an embedded initial fact of `q` is `some 0`
(established at cost 0 by the free `init` action, whose precondition `i` is always `some 0`).
-/
lemma ignf_step_embed {n : ℕ} (q : PlanningTask n) (V : _root_.Vector (WithTop ℕ) (n + 2))
    (W : _root_.Vector (WithTop ℕ) n)
    (hVi : V[(⟨n, by omega⟩ : Fin (n + 2))] = some 0)
    (hWV : ∀ j : Fin n, W[j] = V[(Fin.castLE (show n ≤ n + 2 by omega) j)])
    (f : Fin n) (hf : q.init'[f] = false) :
    (h_1_step (n + 2) (i_g_normal_form q) V)[(Fin.castLE (show n ≤ n + 2 by omega) f)]
      = (h_1_step n q W)[f] := by
  rw [ h_1_step_getElem_contrib, h_1_step_getElem_contrib ];
  have h_filterMap_eq : List.filterMap (fun a => if (Fin.castLE (show n ≤ n + 2 by omega) f) ∈ a.add'.toList then if applicable' a (vec_to_state (n + 2) V) = true then some (actionContribUB V a) else none else none) (i_g_normal_form q).actions' = List.filterMap (fun a => if f ∈ a.add'.toList then if applicable' a (vec_to_state n W) = true then some (actionContribUB W a) else none else none) q.actions' := by
                                                                  have h_filterMap_eq : ∀ a ∈ q.actions', applicable' (Action.mk a.name (toVarSet' (a.pre'.toList.map (Fin.castLE (show n ≤ n + 2 by omega)) ++ [⟨n, by omega⟩])) (toVarSet' (a.add'.toList.map (Fin.castLE (show n ≤ n + 2 by omega)))) (toVarSet' (a.del'.toList.map (Fin.castLE (show n ≤ n + 2 by omega)))) a.cost) (vec_to_state (n + 2) V) ↔ applicable' a (vec_to_state n W) := by
                                                                                                                                                                                                                                                                                                                                                      grind +suggestions;
                                                                  have h_filterMap_eq : ∀ a ∈ q.actions', actionContribUB V (Action.mk a.name (toVarSet' (a.pre'.toList.map (Fin.castLE (show n ≤ n + 2 by omega)) ++ [⟨n, by omega⟩])) (toVarSet' (a.add'.toList.map (Fin.castLE (show n ≤ n + 2 by omega)))) (toVarSet' (a.del'.toList.map (Fin.castLE (show n ≤ n + 2 by omega)))) a.cost) = actionContribUB W a := by
                                                                                                                                                                                                                                                                                                                                                            intros a ha
                                                                                                                                                                                                                                                                                                                                                            simp [actionContribUB, hWV];
                                                                                                                                                                                                                                                                                                                                                            have h_foldl_eq : List.Perm (toVarSet' (a.pre'.toList.map (Fin.castLE (show n ≤ n + 2 by omega)) ++ [⟨n, by omega⟩])).toList (a.pre'.toList.map (Fin.castLE (show n ≤ n + 2 by omega)) ++ [⟨n, by omega⟩]) := by
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          apply List.perm_of_nodup_nodup_toFinset_eq;
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          · exact VarSet'.toList_nodup _;
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          · simp +decide [ List.nodup_append, List.nodup_map_iff_inj_on ];
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            exact ⟨ List.Nodup.map ( fun x y hxy => by simpa [ Fin.ext_iff ] using hxy ) ( a.pre'.toList_nodup ), fun x hx => ne_of_lt ( Fin.castSucc_lt_last x ) ⟩;
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          · ext; simp [toVarSet'];
                                                                                                                                                                                                                                                                                                                                                            have h_foldl_eq : List.foldl max 0 (List.map (fun j => Option.getD V[j] 0) (toVarSet' (a.pre'.toList.map (Fin.castLE (show n ≤ n + 2 by omega)) ++ [⟨n, by omega⟩])).toList) = List.foldl max 0 (List.map (fun j => Option.getD V[j] 0) (a.pre'.toList.map (Fin.castLE (show n ≤ n + 2 by omega)) ++ [⟨n, by omega⟩])) := by
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      apply_rules [ List.Perm.foldl_eq ];
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      exact h_foldl_eq.map _;
                                                                                                                                                                                                                                                                                                                                                            simp_all +decide [ List.foldl_append ];
                                                                                                                                                                                                                                                                                                                                                            congr! 2;
                                                                  unfold i_g_normal_form;
                                                                  simp +zetaDelta at *;
                                                                  rw [ List.filterMap_cons, List.filterMap_cons ] ; simp +decide [ h_filterMap_eq ];
                                                                  rw [ if_neg ( by aesop ) ];
                                                                  rw [ if_neg ( by exact ne_of_lt ( Nat.lt_succ_of_le ( Nat.le_of_lt_succ ( by simp +decide [ Fin.ext_iff ] ) ) ) ) ] ; simp +decide [ h_filterMap_eq ];
                                                                  refine' List.filterMap_congr fun a ha => _;
                                                                  simp +decide [ *, Function.comp ];
  grind

noncomputable def ignf_extend {n : ℕ} (q : PlanningTask n) : _root_.Vector (WithTop ℕ) (n + 2) :=
  _root_.Vector.ofFn (fun idx : Fin (n + 2) =>
    if h : idx.val < n then (ignf_R0 q)[(⟨idx.val, h⟩ : Fin n)]
    else if idx.val = n then some 0
    else if q.goal'.toList.all (fun f => ((ignf_R0 q)[f]).isSome) then
      some ((q.goal'.toList.map (fun f => ((ignf_R0 q)[f]).getD 0)).foldl max 0)
    else none)

/-
`ignf_extend` value at an embedded fact.
-/
lemma ignf_extend_emb {n : ℕ} (q : PlanningTask n) (f : Fin n) :
    (ignf_extend q)[(Fin.castLE (show n ≤ n + 2 by omega) f)] = (ignf_R0 q)[f] := by
  unfold ignf_extend
  simp only [Vector.getElem_ofFn, Fin.coe_castLE, Fin.getElem_fin, dif_pos f.isLt]

/-
`ignf_extend` value at the auxiliary fact `i`.
-/
lemma ignf_extend_i {n : ℕ} (q : PlanningTask n) :
    (ignf_extend q)[(⟨n, by omega⟩ : Fin (n + 2))] = some 0 := by
  unfold ignf_extend
  simp_all only [Fin.getElem_fin, List.all_eq_true, Vector.getElem_ofFn, lt_self_iff_false,
    ↓reduceDIte, ↓reduceIte]

/-
`h_1_step` of the normal form fixes `ignf_extend` at the embedded facts.
-/
lemma ignf_extend_step_emb {n : ℕ} (q : PlanningTask n) (f : Fin n) :
    (h_1_step (n + 2) (i_g_normal_form q) (ignf_extend q))[(Fin.castLE (show n ≤ n + 2 by omega) f)]
      = (ignf_extend q)[(Fin.castLE (show n ≤ n + 2 by omega) f)] := by
                                      by_cases hf : q.init'[f] = true <;> simp_all +decide;
                                      · have h_1_step_zero : (h_1_step (n + 2) (i_g_normal_form q) (ignf_extend q))[(Fin.castLE (show n ≤ n + 2 by omega) f)] = some 0 := by
                                                                                                                                  have h_1_step_zero : (h_1_step (n + 2) (i_g_normal_form q) (ignf_extend q))[(Fin.castLE (show n ≤ n + 2 by omega) f)] ≤ (ignf_extend q)[(Fin.castLE (show n ≤ n + 2 by omega) f)] := by
                                                                                                                                                                                                                                                                                        apply h_1_step_le;
                                                                                                                                  convert h_1_step_zero.antisymm _;
                                                                                                                                  · exact Eq.symm ( ignf_extend_emb q f ▸ q_fix_init q f hf );
                                                                                                                                  · apply h_1_step_ge_of_action_bound;
                                                                                                                                    intro a ha hf h; use ⟨ n, by omega ⟩ ; simp_all +decide [ Fin.ext_iff ] ;
                                                                                                                                    unfold i_g_normal_form at ha; simp_all +decide [ Finset.mem_insert, Finset.mem_singleton ] ;
                                                                                                                                    rcases ha with ( ⟨ a, ha, rfl ⟩ | rfl | rfl ) <;> simp_all +decide [ Finset.mem_insert, Finset.mem_singleton ];
                                                                                                                                    · unfold ignf_extend; simp +decide [ Fin.ext_iff ] ;
                                                                                                                                      exact q_fix_init q f ‹_› ▸ by simp +decide ;
                                                                                                                                    · unfold ignf_extend; simp +decide [ Fin.ext_iff ] ;
                                                                                                                                      exact q_fix_init q f hf ▸ le_rfl;
                                                                                                                                    · exact absurd hf ( by exact ne_of_lt ( Nat.lt_succ_of_le ( Nat.le_of_lt_succ ( by simp +decide [ Fin.ext_iff ] ) ) ) );
                                        convert h_1_step_zero using 1;
                                        convert q_fix_init q f hf using 1;
                                        convert ignf_extend_emb q f using 1;
                                      · convert ignf_step_embed q ( ignf_extend q ) ( ignf_R0 q ) _ _ f hf using 1;
                                        · convert ignf_extend_emb q f using 1;
                                          unfold ignf_R0;
                                          grind +suggestions;
                                        · exact ignf_extend_i q;
                                        · exact fun j => Eq.symm ( ignf_extend_emb q j )

lemma ignf_extend_step_i {n : ℕ} (q : PlanningTask n) :
    (h_1_step (n + 2) (i_g_normal_form q) (ignf_extend q))[(⟨n, by omega⟩ : Fin (n + 2))]
      = (ignf_extend q)[(⟨n, by omega⟩ : Fin (n + 2))] := by
        refine' le_antisymm _ _;
        · exact h_1_step_le (n + 2) (i_g_normal_form q) (ignf_extend q) ⟨n, by omega⟩;
        · refine' h_1_step_ge_of_action_bound _ _ _ _;
          intro a ha hadd happ;
          obtain ⟨q_1, hq_1⟩ : ∃ q_1 ∈ a.pre'.toList, q_1 = ⟨n, by omega⟩ := by
            unfold i_g_normal_form at ha; simp_all +decide [ List.mem_append, List.mem_map ] ;
            rcases ha with ( ⟨ a, ha, rfl ⟩ | rfl | rfl ) <;> simp_all +decide [ toVarSet' ];
          use q_1;
          simp_all +decide [ Fin.ext_iff ]

lemma ignf_extend_step_g {n : ℕ} (q : PlanningTask n) :
    (h_1_step (n + 2) (i_g_normal_form q) (ignf_extend q))[(⟨n + 1, by omega⟩ : Fin (n + 2))]
      = (ignf_extend q)[(⟨n + 1, by omega⟩ : Fin (n + 2))] := by
  -- We'll use the `h_1_step_ge_of_action_bound` lemma for the lower bound, by showing that any applicable action that adds `⟨n+1, _⟩` has a corresponding precondition bound.
  apply le_antisymm (h_1_step_le (n + 2) (i_g_normal_form q) (ignf_extend q) ⟨n + 1, by omega⟩);
  by_cases h : q.goal'.toList = [];
  · unfold ignf_extend; simp_all +decide [ i_g_normal_form ] ;
    finiteness;
  · apply h_1_step_ge_of_action_bound;
    intro a ha hg happ
    obtain ⟨g_star, hg_star⟩ : ∃ g_star ∈ q.goal'.toList, ((ignf_R0 q)[g_star]).isSome ∧ ((ignf_R0 q)[g_star]).getD 0 = (q.goal'.toList.map (fun g => ((ignf_R0 q)[g]).getD 0)).foldl max 0 := by
      have h_foldl_max : ∀ {l : List ℕ}, l ≠ [] → ∃ x ∈ l, x = List.foldl max 0 l := by
        intros l hl_nonempty
        induction' l using List.reverseRecOn with l ih;
        · contradiction;
        · by_cases hl : l = [] <;> simp_all +decide [ List.foldl_append ];
          grind;
      have h_foldl_max : ∀ g ∈ q.goal'.toList, ((ignf_R0 q)[g]).isSome := by
        intro g hg
        have h_applicable : ∀ p ∈ a.pre'.toList, (vec_to_state (n + 2) (ignf_extend q))[p] = true := by
          unfold applicable' at happ; aesop;
        have h_applicable : (vec_to_state (n + 2) (ignf_extend q))[(Fin.castLE (show n ≤ n + 2 by omega) g)] = true := by
                                                                                  have := ignf_action_adds_goal q a ha ‹_›; aesop;
        exact ignf_extend_emb q g ▸ vec_to_state_getElem ( n + 2 ) ( ignf_extend q ) ( Fin.castLE ( show n ≤ n + 2 by omega ) g ) |>.symm ▸ h_applicable ▸ by simp +decide ;
      obtain ⟨ x, hx₁, hx₂ ⟩ := ‹∀ { l : List ℕ }, l ≠ [] → ∃ x ∈ l, x = List.foldl max 0 l› ( show List.map ( fun g => Option.getD ( ignf_R0 q)[g] 0 ) q.goal'.toList ≠ [] from by aesop ) ; use Classical.choose ( List.mem_map.mp hx₁ ) ; have := Classical.choose_spec ( List.mem_map.mp hx₁ ) ; aesop;
    obtain ⟨ha_cost, ha_pre⟩ := ignf_action_adds_goal q a ha hg;
    have h_all_some : ∀ g ∈ q.goal'.toList, ((ignf_R0 q)[g]).isSome := by
      intro g hg; have := happ; simp_all +decide [ applicable' ] ;
      convert happ ( Fin.castLE ( by omega ) g ) _ using 1;
      · grind +suggestions;
      · replace ha_pre := congr_arg List.toFinset ha_pre; rw [ Finset.ext_iff ] at ha_pre; specialize ha_pre ( Fin.castLE ( by omega ) g ) ; aesop;
    simp_all +decide [ ignf_extend ];
    cases h : ( ignf_R0 q)[g_star] <;> aesop

lemma ignf_extend_fixpoint {n : ℕ} (q : PlanningTask n) :
    h_1_step (n + 2) (i_g_normal_form q) (ignf_extend q) = ignf_extend q := by
      ext i;
      by_cases hi : i < n;
      · convert ignf_extend_step_emb q ⟨ i, hi ⟩ using 1;
      · rcases eq_or_lt_of_le ( Nat.le_of_not_lt hi ) with rfl | hi <;> simp_all +arith +decide;
        · convert ignf_extend_step_i q using 1;
        · norm_num [ show i = n + 1 by linarith ];
          convert ignf_extend_step_g q using 1

/-
The normal form's `h_1` fixpoint value at an embedded *initial* fact of `q` is `some 0`
(the free `init` action, applicable since `i` is `some 0`, drives it down to `0`).
-/
lemma ignf_fix_emb_init {n : ℕ} (q : PlanningTask n) (j : Fin n) (hj : q.init'[j] = true) :
    (ignf_RN q)[(Fin.castLE (show n ≤ n + 2 by omega) j)] = some 0 := by
  -- Let `R := ignf_RN q` be the `h_1` fixpoint of the normal form `i_g_normal_form q`.
  set R := ignf_RN q
  have hR : h_1_step (n + 2) (i_g_normal_form q) R = R := by
    exact h_1_iter_fix_is_fixpoint ( n + 2 ) ( i_g_normal_form q ) ( h_1_base ( n + 2 ) ( i_g_normal_form q ).init' );
  -- To bound `R[emb j] ≤ some 0`, apply `fixpoint_value_le_action_cost` to the `init` action of `i_g_normal_form q`.
  have h_init_action : ∃ a : Action (n + 2), a ∈ (i_g_normal_form q).actions' ∧ (Fin.castLE (show n ≤ n + 2 by omega) j) ∈ a.add'.toList ∧ a.cost = 0 ∧ a.pre'.toList = [⟨n, by omega⟩] := by
                                                                                              refine' ⟨ Action.mk "init" ( singletonVarSet ⟨ n, by omega ⟩ ) ( toVarSet' ( q.init'.toList.map ( Fin.castLE ( show n ≤ n + 2 by omega ) ) ) ) ∅ 0, _, _, _, _ ⟩ <;> simp +decide [ i_g_normal_form ];
                                                                                              · exact hj;
                                                                                              · unfold singletonVarSet;
                                                                                                unfold toVarSet'; simp +decide [ mem_toVarSet' ] ;
                                                                                                rfl;
  obtain ⟨a, ha_mem, ha_add, ha_cost, ha_pre⟩ := h_init_action
  have h_applicable : applicable' a (vec_to_state (n + 2) R) = true := by
    have h_applicable : R[(⟨n, by omega⟩ : Fin (n + 2))] = some 0 := by
      convert ignf_fix_i q using 1;
    grind +suggestions;
  have h_bound : R[(Fin.castLE (show n ≤ n + 2 by omega) j)] ≤ some 0 := by
                                  convert fixpoint_value_le_action_cost ( i_g_normal_form q ) R hR a ha_mem ( Fin.castLE ( show n ≤ n + 2 by omega ) j ) ha_add h_applicable using 1;
                                  simp +decide [ ha_cost, ha_pre ];
                                  simp +decide [ ha_pre, List.attach ];
                                  simp +decide [ List.max ];
                                  exact Eq.symm ( ignf_fix_i q );
  cases h : R[(Fin.castLE (show n ≤ n + 2 by omega) j)] <;> simp_all +decide [ Fin.castLE ];
  cases ‹ℕ› <;> norm_cast at *

/-- Restriction of the normal form's `h_1` fixpoint to the embedded facts of `q`. -/
noncomputable def ignf_W {n : ℕ} (q : PlanningTask n) : _root_.Vector (WithTop ℕ) n :=
  _root_.Vector.ofFn (fun j => (ignf_RN q)[(Fin.castLE (show n ≤ n + 2 by omega) j)])

@[simp] lemma ignf_W_getElem {n : ℕ} (q : PlanningTask n) (j : Fin n) :
    (ignf_W q)[j] = (ignf_RN q)[(Fin.castLE (show n ≤ n + 2 by omega) j)] := by
  simp [ignf_W]

/-
The restriction `ignf_W` of the normal form's fixpoint is a fixpoint of `q`'s `h_1_step`.
-/
lemma ignf_W_is_fixpoint {n : ℕ} (q : PlanningTask n) :
    h_1_step n q (ignf_W q) = ignf_W q := by
  apply Vector.ext;
  intro i hi; by_cases hi' : q.init'[(⟨i, hi⟩ : Fin n)] = true <;> simp_all +decide [ Fin.castLE ] ;
  · -- Since `q.init'[i] = true`, we have `(ignf_W q)[i] = some 0`.
    have h_ignf_W_i : (ignf_W q)[(⟨i, hi⟩ : Fin n)] = some 0 := by
      convert ignf_fix_emb_init q ⟨ i, hi ⟩ hi' using 1;
      convert ignf_W_getElem q ⟨ i, hi ⟩ using 1;
    -- Since `q.init'[i] = true`, we have `(h_1_step n q (ignf_W q))[i] ≤ some 0`.
    have h_h1_step_le : (h_1_step n q (ignf_W q))[(⟨i, hi⟩ : Fin n)] ≤ some 0 := by
      exact h_1_step_le n q ( ignf_W q ) ⟨ i, hi ⟩ |> le_trans <| by aesop;
    cases h : ( h_1_step n q ( ignf_W q ) )[(⟨i, hi⟩ : Fin n)] <;> simp_all +decide [ Fin.castLE ];
    exact le_antisymm h_h1_step_le ( Nat.cast_le.mpr ( Nat.zero_le _ ) );
  · convert ignf_step_embed q ( ignf_RN q ) ( ignf_W q ) ( ignf_fix_i q ) ( ignf_W_getElem q ) ⟨ i, hi ⟩ hi' using 1;
    · convert ignf_step_embed q ( ignf_RN q ) ( ignf_W q ) ( ignf_fix_i q ) ( ignf_W_getElem q ) ⟨ i, hi ⟩ hi' |> Eq.symm using 1;
    · convert ignf_step_embed q ( ignf_RN q ) ( ignf_W q ) _ _ ( ⟨ i, hi ⟩ : Fin n ) hi' using 1;
      · convert ignf_W_getElem q ⟨ i, hi ⟩ using 1;
        exact h_1_iter_fix_is_fixpoint ( n + 2 ) ( i_g_normal_form q ) ( h_1_base ( n + 2 ) ( i_g_normal_form q ).init' ) ▸ rfl;
      · exact ignf_fix_i q;
      · grind +suggestions

/-
The restriction `ignf_W` lies below `q`'s base vector.
-/
lemma ignf_W_le_base {n : ℕ} (q : PlanningTask n) (j : Fin n) :
    (ignf_W q)[j] ≤ (h_1_base n q.init')[j] := by
  by_cases h : q.init'[j] = true <;> simp_all +decide [ ignf_W ];
  · have := ignf_fix_emb_init q j h; simp_all +decide [ h_1_base ] ;
  · unfold h_1_base; simp +decide [ h ] ;
    exact le_top

/-- Embedded facts: the normal form's fixpoint value is at most `q`'s fixpoint value. -/
lemma ignf_fix_emb_le {n : ℕ} (q : PlanningTask n) (j : Fin n) :
    (ignf_RN q)[(Fin.castLE (show n ≤ n + 2 by omega) j)] ≤ (ignf_R0 q)[j] := by
  have h := h_1_iter_fix_ge_of_fixpoint q (h_1_base n q.init') (ignf_W q)
    (ignf_W_is_fixpoint q) (ignf_W_le_base q) j
  rw [ignf_W_getElem] at h
  exact h

/-
The explicit extension lies below the normal form's fixpoint (it is a fixpoint below the
normal form's base).
-/
lemma ignf_extend_le_fix {n : ℕ} (q : PlanningTask n) (idx : Fin (n + 2)) :
    (ignf_extend q)[idx] ≤ (ignf_RN q)[idx] := by
  convert h_1_iter_fix_ge_of_fixpoint ( i_g_normal_form q ) ( h_1_base ( n + 2 ) ( i_g_normal_form q ).init' ) ( ignf_extend q ) ( ignf_extend_fixpoint q ) _ idx using 1;
  unfold h_1_base;
  intro i; by_cases hi : i.val = n <;> simp_all +decide [ Fin.ext_iff, i_g_normal_form, PlanningTask.init' ] ;
  · exact ignf_extend_i q ▸ le_rfl;
  · exact le_top

/-- The goal fact `g`: the normal form's fixpoint value is at most the explicit extension value. -/
lemma ignf_fix_g_le {n : ℕ} (q : PlanningTask n) :
    (ignf_RN q)[(⟨n + 1, by omega⟩ : Fin (n + 2))] ≤ (ignf_extend q)[(⟨n + 1, by omega⟩ : Fin (n + 2))] := by
  by_cases h_all : q.goal'.toList.all (fun f => ((ignf_R0 q)[f]).isSome)
  · obtain ⟨a, ha_mem, ha_add, ha_cost, ha_pre⟩ :
        ∃ a : Action (n + 2), a ∈ (i_g_normal_form q).actions' ∧
          (⟨n + 1, by omega⟩ : Fin (n + 2)) ∈ a.add'.toList ∧ a.cost = 0 ∧
          a.pre'.toList = q.goal'.toList.map (Fin.castLE (show n ≤ n + 2 by omega)) := by
      unfold i_g_normal_form; simp +decide [ List.mem_append, List.mem_map ]
      refine' ⟨ _, Or.inr <| Or.inr rfl, _, _, _ ⟩ <;> simp +decide [ singletonVarSet, toVarSet' ]
      unfold VarSet'.toList; simp +decide [ Finset.sort ]
      rw [ List.dedup_eq_self.mpr ]
      · rw [ List.mergeSort_eq_self ]
        simp +decide [ List.pairwise_map, List.pairwise_iff_get ]
        grind +suggestions
      · exact List.Nodup.map ( fun x y hxy => by simpa [ Fin.ext_iff ] using hxy ) ( q.goal'.toList_nodup )
    have hsome : ∀ g ∈ q.goal'.toList, ((ignf_R0 q)[g]).isSome := fun g hg => List.all_eq_true.mp h_all g hg
    have h_applicable : applicable' a (vec_to_state (n + 2) (ignf_RN q)) = true := by
      unfold applicable' satisfies'
      simp only [decide_eq_true_eq]
      intro i hi
      have hi' : i ∈ a.pre'.toList := VarSet'.mem_toList.mp hi
      rw [ha_pre] at hi'
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hi'
      rw [vec_to_state_getElem]
      have hle := ignf_fix_emb_le q g
      obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp (hsome g hg)
      rw [hk] at hle
      rcases hR : (ignf_RN q)[Fin.castLE (show n ≤ n + 2 by omega) g] with _ | v
      · rw [hR] at hle; exact absurd hle (not_le.mpr (WithTop.coe_lt_top k))
      · rfl
    have hb := fixpoint_value_le_action_cost (i_g_normal_form q) (ignf_RN q)
      (h_1_iter_fix_is_fixpoint (n + 2) (i_g_normal_form q) (h_1_base (n + 2) (i_g_normal_form q).init'))
      a ha_mem ⟨n + 1, by omega⟩ ha_add h_applicable
    have hFval : (ignf_extend q)[(⟨n + 1, by omega⟩ : Fin (n + 2))]
        = some ((q.goal'.toList.map (fun f => ((ignf_R0 q)[f]).getD 0)).foldl max 0) := by
      unfold ignf_extend
      rw [Fin.getElem_fin, Vector.getElem_ofFn]
      rw [dif_neg (by simp), if_neg (by simp), if_pos h_all]
    rw [hFval]
    refine le_trans hb ?_
    rw [ha_cost]
    have hgetD_mono : ∀ g ∈ q.goal'.toList,
        ((ignf_RN q)[Fin.castLE (show n ≤ n + 2 by omega) g]).getD 0 ≤ ((ignf_R0 q)[g]).getD 0 :=
      fun g hg => withTop_getD_le_getD (ignf_fix_emb_le q g) (hsome g hg)
    split_ifs with hL
    · exact WithTop.coe_le_coe.mpr (Nat.zero_le _)
    · rw [Nat.zero_add, list_max_eq_foldl_max_zero _ hL]
      refine WithTop.coe_le_coe.mpr ?_
      calc (a.pre'.toList.attach.map (fun x => (ignf_RN q)[x.1].get
                (vec_to_state_isSome_of_applicable (n + 2) (ignf_RN q) a h_applicable x.1 x.2))).foldl max 0
          = (a.pre'.toList.map (fun j => ((ignf_RN q)[j]).getD 0)).foldl max 0 := by
            congr 1
            rw [← List.attach_map_val (l := a.pre'.toList)
              (f := fun j => ((ignf_RN q)[j]).getD 0)]
            apply List.map_congr_left
            intro x _
            exact Option.get_eq_getD ((ignf_RN q)[x.1])
        _ = (q.goal'.toList.map (fun g => ((ignf_RN q)[Fin.castLE (show n ≤ n + 2 by omega) g]).getD 0)).foldl max 0 := by
            rw [ha_pre, List.map_map]; rfl
        _ ≤ (q.goal'.toList.map (fun g => ((ignf_R0 q)[g]).getD 0)).foldl max 0 :=
            foldl_max_mono _ _ _ hgetD_mono
  · have : (ignf_extend q)[(⟨n + 1, by omega⟩ : Fin (n + 2))] = none := by
      unfold ignf_extend
      rw [Fin.getElem_fin, Vector.getElem_ofFn]
      rw [dif_neg (by simp), if_neg (by simp), if_neg h_all]
    rw [this]; exact le_top

/-- The `h_1` fixpoint of the i/g normal form reached from its own base coincides with the explicit
extension `ignf_extend` of `q`'s fixpoint. -/
lemma ignf_RN_eq_extend {n : ℕ} (q : PlanningTask n) :
    ignf_RN q = ignf_extend q := by
  ext idx hidx
  rcases lt_trichotomy idx n with hlt | heq | hgt
  · have key : (ignf_RN q)[(Fin.castLE (show n ≤ n + 2 by omega) ⟨idx, hlt⟩)]
        = (ignf_extend q)[(Fin.castLE (show n ≤ n + 2 by omega) ⟨idx, hlt⟩)] := by
      rw [ignf_extend_emb]
      refine le_antisymm (ignf_fix_emb_le q ⟨idx, hlt⟩) ?_
      have h2 := ignf_extend_le_fix q (Fin.castLE (show n ≤ n + 2 by omega) ⟨idx, hlt⟩)
      rwa [ignf_extend_emb] at h2
    simpa using key
  · have key : (ignf_RN q)[(⟨n, by omega⟩ : Fin (n + 2))]
        = (ignf_extend q)[(⟨n, by omega⟩ : Fin (n + 2))] := by
      unfold ignf_RN
      rw [ignf_fix_i, ignf_extend_i]
    simp only [Fin.getElem_fin] at key
    simpa [heq] using key
  · have hidx1 : idx = n + 1 := by omega
    have key := ignf_fix_g_le q
    have key2 := ignf_extend_le_fix q (⟨n + 1, by omega⟩ : Fin (n + 2))
    have heq2 : (ignf_RN q)[(⟨n + 1, by omega⟩ : Fin (n + 2))]
        = (ignf_extend q)[(⟨n + 1, by omega⟩ : Fin (n + 2))] := le_antisymm key key2
    simp only [Fin.getElem_fin] at heq2
    simpa [hidx1] using heq2

lemma ignf_fix_embed {n : ℕ} (q : PlanningTask n) (f : Fin n) :
    (ignf_RN q)[(Fin.castLE (show n ≤ n + 2 by omega) f)] = (ignf_R0 q)[f] := by
  rw [ignf_RN_eq_extend, ignf_extend_emb]

lemma ignf_fix_embed_init {n : ℕ} (q : PlanningTask n) (f : Fin n) (hf : q.init'[f] = true) :
    (ignf_RN q)[(Fin.castLE (show n ≤ n + 2 by omega) f)] = some 0 := by
  rw [ignf_fix_embed]; exact q_fix_init q f hf

lemma ignf_goal_foldl_eq {n : ℕ} (q : PlanningTask n)
    (h : satisfies' q.goal' (vec_to_state n (ignf_R0 q)) = true) :
    (q.goal'.toList.map (fun f => ((ignf_R0 q)[f]).getD 0)).foldl max 0 = h_1 q q.init' := by
  rw [h_1];
  have h_pre_cost : ∀ f ∈ q.goal'.toList, ((ignf_R0 q)[f]).isSome = true := by
    grind +suggestions;
  split_ifs;
  · have h_pre_cost_eq : q.goal'.toList.map (fun f => ((h_1_iter_fix n q (h_1_base n q.init'))[f]).getD 0) = q.goal'.toList.attach.map (fun x => ((h_1_iter_fix n q (h_1_base n q.init'))[x.1]).get (h_pre_cost x.1 x.2)) := by
      refine' List.ext_get _ _ <;> simp +decide [ List.getElem?_eq_getElem ];
      intro i hi₁ hi₂; specialize h_pre_cost ( q.goal'.toList[i] ) ; simp_all +decide [ Option.isSome_iff_exists ] ;
      unfold ignf_R0 at h_pre_cost; aesop;
    cases h : q.goal'.toList.attach <;> simp_all +decide [ List.max ];
    simp_all +decide [ ignf_R0 ];
  · contradiction

lemma h_1_le_maxFinite_of_satisfies {n : ℕ} (q : PlanningTask n)
    (h : satisfies' q.goal' (vec_to_state n (ignf_R0 q)) = true) :
    h_1 q q.init' ≤ Vector.maxFinite (ignf_R0 q) := by
  rw [ ← ignf_goal_foldl_eq q h ];
  -- By definition of `Vector.maxFinite`, we know that every element in the list is less than or equal to `Vector.maxFinite (ignf_R0 q)`.
  have h_le_maxFinite : ∀ f ∈ q.goal'.toList, ((ignf_R0 q)[f]).getD 0 ≤ Vector.maxFinite (ignf_R0 q) := by
    intro f hf; by_cases h : ( ignf_R0 q)[f] = none <;> simp_all +decide ;
    obtain ⟨ c, hc ⟩ := Option.ne_none_iff_exists'.mp h;
    exact hc.symm ▸ Vector.le_maxFinite hc;
  have h_foldl_le_maxFinite : ∀ (l : List ℕ), (∀ x ∈ l, x ≤ Vector.maxFinite (ignf_R0 q)) → List.foldl max 0 l ≤ Vector.maxFinite (ignf_R0 q) := by
    intro l hl; induction' l using List.reverseRecOn with l ih <;> aesop;
  exact h_foldl_le_maxFinite _ fun x hx => by obtain ⟨ f, hf, rfl ⟩ := List.mem_map.mp hx; exact h_le_maxFinite f hf;

lemma ignf_fix_goal_isSome {n : ℕ} (q : PlanningTask n) :
    ((ignf_RN q)[(⟨n + 1, by omega⟩ : Fin (n + 2))]).isSome
      = satisfies' q.goal' (vec_to_state n (ignf_R0 q)) := by
  unfold satisfies';
  rw [ ignf_RN_eq_extend, ignf_extend ];
  simp +decide [ Fin.add_def, Nat.mod_eq_of_lt ];
  split_ifs <;> simp_all +decide [ vec_to_state_getElem ]

lemma ignf_fix_goal_value {n : ℕ} (q : PlanningTask n)
    (h : satisfies' q.goal' (vec_to_state n (ignf_R0 q)) = true) :
    (ignf_RN q)[(⟨n + 1, by omega⟩ : Fin (n + 2))] = some (h_1 q q.init') := by
  rw [ ← ignf_goal_foldl_eq q h ];
  refine' ignf_RN_eq_extend q ▸ _;
  convert Vector.getElem_ofFn _ using 1;
  have := ignf_fix_goal_isSome q; simp_all +decide [ Fin.ext_iff, vec_to_state_getElem, satisfies'_iff ] ;

lemma maxFinite_le {m : ℕ} (v : _root_.Vector (WithTop ℕ) m) (B : ℕ)
    (h : ∀ i : Fin m, ∀ c : ℕ, v[i] = some c → c ≤ B) : Vector.maxFinite v ≤ B := by
  induction v using Vector.recOn ; simp_all [ Vector.maxFinite ]
  have h_foldl_le_B : ∀ (l : List (WithTop ℕ)), (∀ x ∈ l, ∀ c, x = some c → c ≤ B) → List.foldl (fun acc x => match x with | some c => max acc c | none => acc) 0 l ≤ B := by
    intro l hl
    induction' l using List.reverseRecOn with l ih
    · exact Nat.zero_le _
    · grind +extAll
  convert h_foldl_le_B ( List.map ( fun i : Fin m => ‹Array ( WithTop ℕ ) ›[i] ) ( List.finRange m ) ) _ using 1
  · rw [ ← List.foldl_toArray ]
    congr
    · grind +qlia
    · simp [ * ]
  · grind

/-
The maximal finite fixpoint value is preserved by the normal form (the auxiliary `i = some 0`
and goal `g` facts do not increase it, and the embedded facts carry exactly q's values).
-/
lemma ignf_maxFinite_eq {n : ℕ} (q : PlanningTask n) :
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
      · have := ignf_fix_i q; simp_all
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
/-- Replacing a task's goal by its own goal is the identity. -/
lemma replace_goal_self {n : ℕ} (prob : PlanningTask n) :
    replace_goal prob prob.goal' = prob := by
  cases prob; rfl

/-- Direct (non-`replace_goal`) form of `h_1_eq_maxFinite_of_not_satisfies`. -/
lemma h_1_self_eq_maxFinite_of_not_satisfies {n : ℕ} (prob : PlanningTask n)
    (hns : ¬ satisfies' prob.goal'
        (vec_to_state n (h_1_iter_fix n prob (h_1_base n prob.init'))) = true) :
    h_1 prob prob.init'
      = Vector.maxFinite (h_1_iter_fix n prob (h_1_base n prob.init')) + 1 := by
  have := h_1_eq_maxFinite_of_not_satisfies prob prob.goal' prob.init' hns
  rwa [replace_goal_self] at this

lemma h_1_i_g_normal_form_eq {n : ℕ} (q : PlanningTask n) :
    h_1 (i_g_normal_form q) (i_g_normal_form q).init' = h_1 q q.init' := by
  have hgoal : (i_g_normal_form q).goal' = singletonVarSet ⟨n + 1, by omega⟩ := rfl
  by_cases h : satisfies' q.goal' (vec_to_state n (ignf_R0 q)) = true
  · have hsome : ((ignf_RN q)[(⟨n + 1, by omega⟩ : Fin (n + 2))]).isSome := by
      rw [ignf_fix_goal_isSome]; exact h
    have h1n := h_1_singleton_eq_getD (i_g_normal_form q) ⟨n + 1, by omega⟩
      (i_g_normal_form q).init' hsome
    rw [← hgoal, replace_goal_self] at h1n
    have hv := ignf_fix_goal_value q h
    simp only [ignf_RN] at hv
    rw [h1n, hv]; rfl
  · have hns_normal : ((ignf_RN q)[(⟨n + 1, by omega⟩ : Fin (n + 2))]).isSome = false := by
      rw [ignf_fix_goal_isSome]; rw [Bool.not_eq_true] at h; exact h
    simp only [ignf_RN] at hns_normal
    have lhs : h_1 (i_g_normal_form q) (i_g_normal_form q).init'
        = Vector.maxFinite (ignf_RN q) + 1 := by
      apply h_1_self_eq_maxFinite_of_not_satisfies
      rw [hgoal, satisfies'_singleton, vec_to_state_getElem, hns_normal]
      decide
    have rhs : h_1 q q.init' = Vector.maxFinite (ignf_R0 q) + 1 := by
      apply h_1_self_eq_maxFinite_of_not_satisfies
      simpa [ignf_R0] using h
    rw [lhs, rhs, ignf_maxFinite_eq]

/-
`h_1` does not depend on a task's initial state field (only on the state argument, actions and
goal), so overwriting the initial state is irrelevant.
-/
lemma h_1_set_init_eq {n : ℕ} (prob : PlanningTask n) (s : State' n) :
    h_1 (set_init prob s) s = h_1 prob s := by
  convert h_1_set_init prob s s using 1

lemma h1_goal_value_normal_form {n : ℕ} (prob : PlanningTask n) (s : State' n)
    (hg : prob.goal'.toList ≠ []) :
    h1_goal_value (i_g_normal_form (set_init prob s))
        (get_unitary_goal (i_g_normal_form (set_init prob s))
          (i_g_normalform_is_unitary_goal _))
      = h_1 prob s := by
  -- Let P := set_init prob s.
  set P : PlanningTask n := set_init prob s;
  convert h_1_i_g_normal_form_eq P using 1;
  · have := get_unitary_goal_is_goal ( i_g_normal_form P ) ( i_g_normalform_is_unitary_goal P );
    replace this := congr_arg List.toFinset this; rw [ Finset.ext_iff ] at this; specialize this ⟨ n + 1, by omega ⟩ ; simp_all +decide ;
    exact this.mp ( by simp +decide [ i_g_normal_form ] ) ▸ rfl;
  · convert h_1_set_init_eq prob s |> Eq.symm

lemma h_1_of_empty_goal {n : ℕ} (prob : PlanningTask n) (s : State' n) (hg : prob.goal'.toList = []) :
    h_1 prob s = 0 := by
  -- Since the goal is empty, the h_1 of the original problem is 0 by definition.
  simp [h_1, hg];
  -- Since the goal is empty, there are no elements i in the goal. Therefore, the implication holds vacuously because there are no elements to check. We can use the fact that the goal is empty to derive a contradiction.
  intro i hi
  have := hg
  simp_all +decide [ Finset.ext_iff ];
  replace this := congr_arg List.toFinset this; rw [ Finset.ext_iff ] at this; specialize this i; aesop;

theorem lmcut_h1_dominates {n : ℕ} (prob : PlanningTask n) (s : State' n)
    (plan : Plan prob (convertState s)) :
    lmcut prob s (@h1_pcf n) ≥ (h_1 prob s : ℕ∞) := by
  rw [lmcut]
  split
  · -- empty goal: `h_1 prob s = 0`
    rename_i hg
    exact_mod_cast (h_1_of_empty_goal prob s hg).le
  · rename_i hg
    -- lift the plan to a plan of the i/g normal form of `set_init prob s`
    obtain ⟨p', hp'⟩ := path_set_init_transfer prob s plan.path
    obtain ⟨eplan, _⟩ := ignf_plan_lift (set_init prob s) ⟨plan.last, p', plan.goal⟩
    have hcore := lmcut_inner_ge_h1_goal _ (i_g_normal_form (set_init prob s))
      (i_g_normalform_is_unitary_init _) (i_g_normalform_is_unitary_goal _)
      (i_g_normal_form_has_preconditions (set_init prob s) hg) rfl eplan
    rw [h1_goal_value_normal_form prob s hg] at hcore
    exact hcore

end STRIPS