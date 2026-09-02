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
    (h_1_iter (i_g_normal_form q) (h_1_base (n + 2) (i_g_normal_form q).init'.toBitVec) k)[(⟨n, by omega⟩ : Fin (n + 2))]
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
lemma q_init_fact_iter {n : ℕ} (q : PlanningTask n) (k : ℕ) (g : Fin n) (hg : q.init'.toBitVec[g] = true) :
    (h_1_iter q (h_1_base n q.init'.toBitVec) k)[g] = some 0 := by
      induction' k with k ih;
      · unfold h_1_iter h_1_base; aesop;
      · refine' le_antisymm _ _ <;> simp_all +decide [ h_1_iter ];
        · refine' le_trans ( h_1_step_le _ _ _ _ ) _;
          exact ih.le;
        · finiteness

lemma ignf_fix_i {n : ℕ} (q : PlanningTask n) :
    (h_1_iter_fix (n + 2) (i_g_normal_form q)
        (h_1_base (n + 2) (i_g_normal_form q).init'.toBitVec))[(⟨n, by omega⟩ : Fin (n + 2))] = some 0 := by
  obtain ⟨K, hK⟩ := h_1_iter_eventually_fix (i_g_normal_form q)
    (h_1_base (n + 2) (i_g_normal_form q).init'.toBitVec)
  rw [← hK]; exact ignf_i_fact_iter q K

/-- q's `h_1` fixpoint vector (the deflation limit from the base of q's initial state). -/
noncomputable def ignf_R0 {n : ℕ} (q : PlanningTask n) : _root_.Vector (WithTop ℕ) n :=
  h_1_iter_fix n q (h_1_base n q.init'.toBitVec)

/-- The i/g normal form's `h_1` fixpoint vector. -/
noncomputable def ignf_RN {n : ℕ} (q : PlanningTask n) : _root_.Vector (WithTop ℕ) (n + 2) :=
  h_1_iter_fix (n + 2) (i_g_normal_form q) (h_1_base (n + 2) (i_g_normal_form q).init'.toBitVec)

/-
The only actions of the normal form that add the goal fact `g = ⟨n+1⟩` are (copies of) the
`goal` action: any such action is free and has the embedded goal of `q` as its precondition.
-/
/-- A strictly increasing (sorted) list of variables is recovered exactly by `VarSet.ofList`. -/
lemma VarSet.toList_ofList_sortedLT {m : ℕ} (l : List (Fin m)) (hl : l.Pairwise (· < ·)) :
    (VarSet.ofList l).toList = l := by
  have hval : (VarSet.ofList l).toList = (List.finRange m).filter (· ∈ VarSet.ofList l) := rfl
  rw [hval]
  have hfin : ((List.finRange m).filter (· ∈ VarSet.ofList l)).Pairwise (· < ·) :=
    List.Pairwise.sublist (List.filter_sublist)
      ((List.sortedLT_iff_pairwise).mp (List.sortedLT_finRange m))
  apply List.Pairwise.eq_of_mem_iff hfin hl
  intro a
  simp [List.mem_filter, List.mem_finRange, VarSet.mem_ofList]

/-- Embedding a variable set's list via `Fin.castLE` keeps it strictly sorted. -/
lemma toList_map_castLE_pairwise {n : ℕ} (V : VarSet n) :
    (V.toList.map (Fin.castLE (show n ≤ n+2 by omega))).Pairwise (· < ·) := by
  have hV : V.toList.Pairwise (· < ·) :=
    List.Pairwise.sublist (List.filter_sublist)
      ((List.sortedLT_iff_pairwise).mp (List.sortedLT_finRange n))
  rw [List.pairwise_map]
  refine hV.imp ?_
  intro a b hab
  simp only [Fin.lt_def, Fin.val_castLE]
  exact hab

lemma ignf_action_adds_goal {n : ℕ} (q : PlanningTask n) (a : Action (n + 2))
    (ha : a ∈ (i_g_normal_form q).actions')
    (hg : (⟨n + 1, by omega⟩ : Fin (n + 2)) ∈ a.add.toList) :
    a.cost = 0 ∧
      a.pre.toList = q.goal'.toList.map (Fin.castLE (show n ≤ n + 2 by omega)) := by
  unfold i_g_normal_form at ha
  simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with ⟨a0, ha0, rfl⟩ | rfl | rfl
  · exfalso
    rw [VarSet.mem_toList_iff, VarSet.mem_ofList, List.mem_map] at hg
    obtain ⟨x, _, hx⟩ := hg
    have : (Fin.castLE (show n ≤ n+2 by omega) x).val = n + 1 := by rw [hx]
    simp only [Fin.val_castLE] at this; omega
  · exfalso
    rw [VarSet.mem_toList_iff, VarSet.mem_ofList, List.mem_map] at hg
    obtain ⟨x, _, hx⟩ := hg
    have : (Fin.castLE (show n ≤ n+2 by omega) x).val = n + 1 := by rw [hx]
    simp only [Fin.val_castLE] at this; omega
  · exact ⟨rfl, VarSet.toList_ofList_sortedLT _ (toList_map_castLE_pairwise q.goal')⟩
lemma q_fix_init {n : ℕ} (q : PlanningTask n) (f : Fin n) (hf : q.init'.toBitVec[f] = true) :
    (ignf_R0 q)[f] = some 0 := by
  have := STRIPS.h_1_iter_eventually_fix q ( STRIPS.h_1_base n q.init'.toBitVec )
  convert q_init_fact_iter q this.choose f hf
  exact this.choose_spec.symm

/-
The normal form's `h_1` fixpoint value at an embedded initial fact of `q` is `some 0`
(established at cost 0 by the free `init` action, whose precondition `i` is always `some 0`).
-/
/-- The embedded action of the normal form adds an embedded fact iff the original does. -/
lemma ignf_map_add_iff {n : ℕ} (b : Action n) (f : Fin n) :
    (Fin.castLE (show n ≤ n+2 by omega) f) ∈
      (VarSet.ofList (b.add.toList.map (Fin.castLE (show n ≤ n+2 by omega)))).toList
    ↔ f ∈ b.add.toList := by
  rw [VarSet.mem_toList_iff, VarSet.mem_ofList, List.mem_map]
  constructor
  · rintro ⟨x, hx, hxe⟩
    obtain rfl := Fin.castLE_injective _ hxe
    exact hx
  · exact fun hf => ⟨f, hf, rfl⟩

/-- Applicability of the embedded action at `V` matches applicability of the original at `W`. -/
lemma ignf_map_applicable {n : ℕ} (V : _root_.Vector (WithTop ℕ) (n + 2))
    (W : _root_.Vector (WithTop ℕ) n)
    (hVi : V[(⟨n, by omega⟩ : Fin (n + 2))] = some 0)
    (hWV : ∀ j : Fin n, W[j] = V[(Fin.castLE (show n ≤ n + 2 by omega) j)]) (b : Action n) :
    applicable' (⟨b.name,
        VarSet.ofList (b.pre.toList.map (Fin.castLE (show n ≤ n+2 by omega)) ++ [⟨n, by omega⟩]),
        VarSet.ofList (b.add.toList.map (Fin.castLE (show n ≤ n+2 by omega))),
        VarSet.ofList (b.del.toList.map (Fin.castLE (show n ≤ n+2 by omega))), b.cost⟩ : Action (n+2))
        (vec_to_state (n+2) V)
      = applicable' b (vec_to_state n W) := by
  set emb := Fin.castLE (show n ≤ n + 2 by omega) with hemb
  simp only [applicable', satisfies', decide_eq_decide]
  constructor
  · intro h x hx
    have hx' : emb x ∈ (VarSet.ofList (b.pre.toList.map emb ++ [(⟨n, by omega⟩ : Fin (n+2))])).val := by
      rw [mem_val_ofList, List.mem_append, List.mem_map]
      exact Or.inl ⟨x, by simpa using hx, rfl⟩
    have := h (emb x) hx'
    rw [vec_to_state_getElem] at this ⊢
    rw [hWV x]; exact this
  · intro h p hp
    rw [mem_val_ofList, List.mem_append, List.mem_map] at hp
    rcases hp with ⟨x, hx, rfl⟩ | hp
    · rw [vec_to_state_getElem, ← hWV x]
      have := h x (by simpa using hx)
      rw [vec_to_state_getElem] at this
      exact this
    · simp only [List.mem_singleton] at hp
      subst hp
      rw [vec_to_state_getElem, hVi]
      rfl

/-- The contribution of the embedded action at `V` matches that of the original at `W`. -/
lemma ignf_map_contribUB {n : ℕ} (V : _root_.Vector (WithTop ℕ) (n + 2))
    (W : _root_.Vector (WithTop ℕ) n)
    (hVi : V[(⟨n, by omega⟩ : Fin (n + 2))] = some 0)
    (hWV : ∀ j : Fin n, W[j] = V[(Fin.castLE (show n ≤ n + 2 by omega) j)]) (b : Action n) :
    actionContribUB V (⟨b.name,
        VarSet.ofList (b.pre.toList.map (Fin.castLE (show n ≤ n+2 by omega)) ++ [⟨n, by omega⟩]),
        VarSet.ofList (b.add.toList.map (Fin.castLE (show n ≤ n+2 by omega))),
        VarSet.ofList (b.del.toList.map (Fin.castLE (show n ≤ n+2 by omega))), b.cost⟩ : Action (n+2))
      = actionContribUB W b := by
  set emb := Fin.castLE (show n ≤ n + 2 by omega) with hemb
  have hsorted : (b.pre.toList.map emb ++ [(⟨n, by omega⟩ : Fin (n+2))]).Pairwise (· < ·) := by
    rw [List.pairwise_append]
    refine ⟨toList_map_castLE_pairwise b.pre, List.pairwise_singleton _ _, ?_⟩
    intro x hx y hy
    simp only [List.mem_singleton] at hy
    subst hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    simp only [hemb, Fin.lt_def, Fin.val_castLE]
    exact z.isLt
  have hpre : (VarSet.ofList (b.pre.toList.map emb ++ [(⟨n, by omega⟩ : Fin (n+2))])).toList
      = b.pre.toList.map emb ++ [(⟨n, by omega⟩ : Fin (n+2))] :=
    VarSet.toList_ofList_sortedLT _ hsorted
  unfold actionContribUB
  simp only [hpre]
  congr 1
  rw [List.map_append, List.foldl_append]
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
  rw [show V[(⟨n, by omega⟩ : Fin (n+2))].getD 0 = 0 from by simp [hVi]]
  rw [Nat.max_zero, List.map_map]
  congr 1
  apply List.map_congr_left
  intro x hx
  simp only [Function.comp_apply]
  rw [hWV x]

lemma ignf_step_embed {n : ℕ} (q : PlanningTask n) (V : _root_.Vector (WithTop ℕ) (n + 2))
    (W : _root_.Vector (WithTop ℕ) n)
    (hVi : V[(⟨n, by omega⟩ : Fin (n + 2))] = some 0)
    (hWV : ∀ j : Fin n, W[j] = V[(Fin.castLE (show n ≤ n + 2 by omega) j)])
    (f : Fin n) (hf : q.init'.toBitVec[f] = false) :
    (h_1_step (n + 2) (i_g_normal_form q) V)[(Fin.castLE (show n ≤ n + 2 by omega) f)]
      = (h_1_step n q W)[f] := by
  set emb := Fin.castLE (show n ≤ n + 2 by omega) with hemb
  rw [h_1_step_getElem_contrib, h_1_step_getElem_contrib]
  have hbase : V[emb f] = W[f] := (hWV f).symm
  have hLeq : (i_g_normal_form q).actions'.filterMap
        (fun a => if emb f ∈ a.add.toList then
          (if applicable' a (vec_to_state (n + 2) V) then some (actionContribUB V a) else none) else none)
      = q.actions'.filterMap
        (fun b => if f ∈ b.add.toList then
          (if applicable' b (vec_to_state n W) then some (actionContribUB W b) else none) else none) := by
    have hact : (i_g_normal_form q).actions'
        = q.actions'.map (fun b => (⟨b.name,
            VarSet.ofList (b.pre.toList.map emb ++ [(⟨n, by omega⟩ : Fin (n+2))]),
            VarSet.ofList (b.add.toList.map emb),
            VarSet.ofList (b.del.toList.map emb), b.cost⟩ : Action (n+2)))
          ++ [(⟨"init", singletonVarSet (⟨n, by omega⟩ : Fin (n+2)),
                VarSet.ofList (q.init'.toList.map emb), (∅ : VarSet (n+2)), 0⟩ : Action (n+2)),
              (⟨"goal", VarSet.ofList (q.goal'.toList.map emb),
                singletonVarSet (⟨n+1, by omega⟩ : Fin (n+2)), (∅ : VarSet (n+2)), 0⟩ : Action (n+2))] := rfl
    rw [hact, List.filterMap_append, List.filterMap_map]
    have hia_none : (fun a : Action (n+2) => if emb f ∈ a.add.toList then
          (if applicable' a (vec_to_state (n + 2) V) then some (actionContribUB V a) else none) else none)
        (⟨"init", singletonVarSet (⟨n, by omega⟩ : Fin (n+2)),
            VarSet.ofList (q.init'.toList.map emb), (∅ : VarSet (n+2)), 0⟩ : Action (n+2)) = none := by
      apply if_neg
      intro hmem
      rw [VarSet.mem_toList_iff, VarSet.mem_ofList, List.mem_map] at hmem
      obtain ⟨x, hx, hxe⟩ := hmem
      obtain rfl := Fin.castLE_injective _ hxe
      rw [VarSet.mem_toList_iff, VarSet.mem_iff, hf] at hx
      exact absurd hx (by simp)
    have hga_none : (fun a : Action (n+2) => if emb f ∈ a.add.toList then
          (if applicable' a (vec_to_state (n + 2) V) then some (actionContribUB V a) else none) else none)
        (⟨"goal", VarSet.ofList (q.goal'.toList.map emb),
            singletonVarSet (⟨n+1, by omega⟩ : Fin (n+2)), (∅ : VarSet (n+2)), 0⟩ : Action (n+2)) = none := by
      apply if_neg
      intro hmem
      rw [VarSet.mem_toList_iff] at hmem
      simp only [singletonVarSet, VarSet.mem_ofList, List.mem_singleton, hemb, Fin.ext_iff,
        Fin.val_castLE] at hmem
      omega
    simp only [List.filterMap_cons, List.filterMap_nil, hia_none, hga_none, List.append_nil]
    apply List.filterMap_congr
    intro b hb
    simp only [Function.comp_apply]
    by_cases hadd : f ∈ b.add.toList
    · rw [if_pos ((ignf_map_add_iff b f).mpr hadd), if_pos hadd,
        ignf_map_applicable V W hVi hWV b, ignf_map_contribUB V W hVi hWV b]
    · rw [if_neg (fun h => hadd ((ignf_map_add_iff b f).mp h)), if_neg hadd]
  rw [hLeq, hbase]
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
  simp only [Vector.getElem_ofFn, Fin.val_castLE, Fin.getElem_fin, dif_pos f.isLt]

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
  by_cases hf : q.init'.toBitVec[f] = true
  · have hval : (ignf_extend q)[(Fin.castLE (show n ≤ n + 2 by omega) f)] = some 0 := by
      rw [ignf_extend_emb]; exact q_fix_init q f hf
    rw [hval]
    refine le_antisymm ?_ ?_
    · rw [← hval]; exact h_1_step_le _ _ _ _
    · cases h : (h_1_step (n + 2) (i_g_normal_form q) (ignf_extend q))[(Fin.castLE (show n ≤ n + 2 by omega) f)] with
      | top => exact le_top
      | coe v => exact WithTop.coe_le_coe.mpr (Nat.zero_le v)
  · have hf' : q.init'.toBitVec[f] = false := by simpa using hf
    have hstep := ignf_step_embed q (ignf_extend q) (ignf_R0 q) (ignf_extend_i q)
      (fun j => (ignf_extend_emb q j).symm) f hf'
    rw [hstep]
    have hR0fix : h_1_step n q (ignf_R0 q) = ignf_R0 q :=
      h_1_iter_fix_is_fixpoint n q (h_1_base n q.init'.toBitVec)
    rw [hR0fix]
    exact (ignf_extend_emb q f).symm
/-- No action of the normal form adds the auxiliary fact `i = ⟨n⟩`. -/
lemma ignf_action_not_adds_i {n : ℕ} (q : PlanningTask n) (a : Action (n + 2))
    (ha : a ∈ (i_g_normal_form q).actions') :
    (⟨n, by omega⟩ : Fin (n + 2)) ∉ a.add.toList := by
  unfold i_g_normal_form at ha
  simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with ⟨a0, ha0, rfl⟩ | rfl | rfl
  · rw [VarSet.mem_toList_iff, VarSet.mem_ofList, List.mem_map]
    rintro ⟨x, _, hx⟩
    have : (Fin.castLE (show n ≤ n+2 by omega) x).val = n := by rw [hx]
    simp only [Fin.val_castLE] at this; omega
  · rw [VarSet.mem_toList_iff, VarSet.mem_ofList, List.mem_map]
    rintro ⟨x, _, hx⟩
    have : (Fin.castLE (show n ≤ n+2 by omega) x).val = n := by rw [hx]
    simp only [Fin.val_castLE] at this; omega
  · rw [VarSet.mem_toList_iff]
    intro hmem
    simp only [singletonVarSet, VarSet.mem_ofList, List.mem_singleton, Fin.ext_iff] at hmem
    omega

lemma ignf_extend_step_i {n : ℕ} (q : PlanningTask n) :
    (h_1_step (n + 2) (i_g_normal_form q) (ignf_extend q))[(⟨n, by omega⟩ : Fin (n + 2))]
      = (ignf_extend q)[(⟨n, by omega⟩ : Fin (n + 2))] := by
  apply le_antisymm (h_1_step_le (n + 2) (i_g_normal_form q) (ignf_extend q) ⟨n, by omega⟩)
  apply h_1_step_ge_of_action_bound
  intro a ha hi happ
  exact absurd hi (ignf_action_not_adds_i q a ha)
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
        have h_applicable : ∀ p ∈ a.pre.toList, (vec_to_state (n + 2) (ignf_extend q))[p] = true := by
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
  have key : ∀ i : Fin (n+2),
      (h_1_step (n + 2) (i_g_normal_form q) (ignf_extend q))[i] = (ignf_extend q)[i] := by
    intro i
    rcases lt_trichotomy i.val n with h | h | h
    · rw [show i = Fin.castLE (show n ≤ n+2 by omega) ⟨i.val, h⟩ from Fin.ext rfl]
      exact ignf_extend_step_emb q _
    · rw [show i = (⟨n, by omega⟩ : Fin (n+2)) from Fin.ext h]
      exact ignf_extend_step_i q
    · have hi : i.val = n + 1 := by have := i.isLt; omega
      rw [show i = (⟨n+1, by omega⟩ : Fin (n+2)) from Fin.ext hi]
      exact ignf_extend_step_g q
  apply Vector.ext
  intro idx hidx
  exact key ⟨idx, hidx⟩
/-- At a fixpoint, the value of a fact is bounded by the contribution of any applicable action
that adds it. -/
lemma fixpoint_le_actionContribUB {n : ℕ} (prob : PlanningTask n) (v : _root_.Vector (WithTop ℕ) n)
    (hfix : h_1_step n prob v = v) (a : Action n) (ha : a ∈ prob.actions')
    (i : Fin n) (hadd : i ∈ a.add.toList) (happ : applicable' a (vec_to_state n v) = true) :
    v[i] ≤ some (actionContribUB v a) := by
  have hisome : (v[i]).isSome := by
    by_contra hcon
    rw [Option.not_isSome_iff_eq_none] at hcon
    have hle0 := h_1_step_le_action_contribution prob v a ha i hadd happ
    rw [show (h_1_step n prob v)[i] = v[i] from congr_arg (·[i]) hfix, hcon,
      WithTop.none_eq_top, top_le_iff] at hle0
    exact absurd hle0 (by simp)
  have hle := fixpoint_get_le_action_cost prob v hfix a ha i hadd happ hisome
  rw [actionContribUB_eq_of_applicable v a happ]
  conv_lhs => rw [← Option.some_get hisome]
  exact WithTop.coe_le_coe.mpr hle

lemma ignf_fix_emb_init {n : ℕ} (q : PlanningTask n) (j : Fin n) (hj : q.init'.toBitVec[j] = true) :
    (ignf_RN q)[(Fin.castLE (show n ≤ n + 2 by omega) j)] = some 0 := by
  set emb := Fin.castLE (show n ≤ n + 2 by omega) with hemb
  set ia : Action (n+2) := ⟨"init", singletonVarSet ⟨n, by omega⟩,
      VarSet.ofList (q.init'.toList.map emb), (∅ : VarSet (n+2)), 0⟩ with hia
  have hmem : ia ∈ (i_g_normal_form q).actions' := by
    unfold i_g_normal_form
    apply List.mem_append_right
    simp [hia, hemb]
  have hjmem : j ∈ q.init'.toList := VarSet.mem_toList_iff.mpr (VarSet.mem_iff.mpr hj)
  have hadd : emb j ∈ ia.add.toList := by
    rw [hia]
    show emb j ∈ (VarSet.ofList (q.init'.toList.map emb)).toList
    rw [VarSet.mem_toList_iff, VarSet.mem_ofList, List.mem_map]
    exact ⟨j, hjmem, rfl⟩
  have hRNfix : h_1_step (n+2) (i_g_normal_form q) (ignf_RN q) = ignf_RN q :=
    h_1_iter_fix_is_fixpoint (n+2) (i_g_normal_form q)
      (h_1_base (n+2) (i_g_normal_form q).init'.toBitVec)
  have hi : (ignf_RN q)[(⟨n, by omega⟩ : Fin (n+2))] = some 0 := ignf_fix_i q
  have happ : applicable' ia (vec_to_state (n+2) (ignf_RN q)) = true := by
    rw [hia]
    show satisfies' (singletonVarSet (⟨n, by omega⟩ : Fin (n+2))) (vec_to_state (n+2) (ignf_RN q)) = true
    rw [satisfies'_singleton, vec_to_state_getElem]
    simp [hi]
  have hval : ((ignf_RN q)[(⟨n, by omega⟩ : Fin (n+2))]).getD 0 = 0 := by simp [hi]
  have hub : actionContribUB (ignf_RN q) ia = 0 := by
    simp only [actionContribUB, hia]
    rw [VarSet.toList_singletonVarSet]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    simp only [Fin.getElem_fin] at hval ⊢
    simp [hval]
  have hle := fixpoint_le_actionContribUB (i_g_normal_form q) (ignf_RN q) hRNfix ia hmem
    (emb j) hadd happ
  rw [hub] at hle
  refine le_antisymm hle ?_
  cases h : (ignf_RN q)[emb j] with
  | top => exact le_top
  | coe c => exact WithTop.coe_le_coe.mpr (Nat.zero_le c)
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
  have hi : (ignf_RN q)[(⟨n, by omega⟩ : Fin (n+2))] = some 0 := ignf_fix_i q
  have hRNfix : h_1_step (n+2) (i_g_normal_form q) (ignf_RN q) = ignf_RN q :=
    h_1_iter_fix_is_fixpoint (n+2) (i_g_normal_form q)
      (h_1_base (n+2) (i_g_normal_form q).init'.toBitVec)
  have key : ∀ j : Fin n, (h_1_step n q (ignf_W q))[j] = (ignf_W q)[j] := by
    intro j
    by_cases hf : q.init'.toBitVec[j] = true
    · have hWj : (ignf_W q)[j] = some 0 := by
        rw [ignf_W_getElem]; exact ignf_fix_emb_init q j hf
      rw [hWj]
      refine le_antisymm ?_ ?_
      · rw [← hWj]; exact h_1_step_le n q (ignf_W q) j
      · cases h : (h_1_step n q (ignf_W q))[j] with
        | top => exact le_top
        | coe v => exact WithTop.coe_le_coe.mpr (Nat.zero_le v)
    · have hf' : q.init'.toBitVec[j] = false := by simpa using hf
      have hstep := ignf_step_embed q (ignf_RN q) (ignf_W q) hi
        (fun k => ignf_W_getElem q k) j hf'
      rw [ignf_W_getElem, ← hstep]
      exact congr_arg (·[Fin.castLE (show n ≤ n + 2 by omega) j]) hRNfix
  apply Vector.ext
  intro idx hidx
  exact key ⟨idx, hidx⟩
lemma ignf_W_le_base {n : ℕ} (q : PlanningTask n) (j : Fin n) :
    (ignf_W q)[j] ≤ (h_1_base n q.init'.toBitVec)[j] := by
  by_cases h : q.init'.toBitVec[j] = true <;> simp_all +decide [ ignf_W ];
  · have := ignf_fix_emb_init q j h; simp_all +decide [ h_1_base ] ;
  · unfold h_1_base; simp +decide [ h ] ;
    exact le_top

/-- Embedded facts: the normal form's fixpoint value is at most `q`'s fixpoint value. -/
lemma ignf_fix_emb_le {n : ℕ} (q : PlanningTask n) (j : Fin n) :
    (ignf_RN q)[(Fin.castLE (show n ≤ n + 2 by omega) j)] ≤ (ignf_R0 q)[j] := by
  have h := h_1_iter_fix_ge_of_fixpoint q (h_1_base n q.init'.toBitVec) (ignf_W q)
    (ignf_W_is_fixpoint q) (ignf_W_le_base q) j
  rw [ignf_W_getElem] at h
  exact h

/-
The explicit extension lies below the normal form's fixpoint (it is a fixpoint below the
normal form's base).
-/
/-- The auxiliary/goal bits of the normal form's initial state: only fact `n` is set. -/
lemma ignf_init_bit {n : ℕ} (q : PlanningTask n) (i : Fin (n+2)) :
    (i_g_normal_form q).init'.toBitVec[i] = decide (i.val = n) := by
  show ((BitVec.zero (n+2) ||| BitVec.twoPow (n+2) n))[i] = decide (i.val = n)
  simp [BitVec.getElem_twoPow]

lemma ignf_extend_le_fix {n : ℕ} (q : PlanningTask n) (idx : Fin (n + 2)) :
    (ignf_extend q)[idx] ≤ (ignf_RN q)[idx] := by
  apply h_1_iter_fix_ge_of_fixpoint (i_g_normal_form q)
    (h_1_base (n + 2) (i_g_normal_form q).init'.toBitVec) (ignf_extend q)
    (ignf_extend_fixpoint q)
  intro i
  rcases eq_or_ne i.val n with h | h
  · have hbase : (h_1_base (n + 2) (i_g_normal_form q).init'.toBitVec)[i] = some 0 := by
      unfold h_1_base
      simp only [ignf_init_bit]
      simp [h]
    rw [hbase, show i = (⟨n, by omega⟩ : Fin (n+2)) from Fin.ext h, ignf_extend_i]
  · have hbase : (h_1_base (n + 2) (i_g_normal_form q).init'.toBitVec)[i] = none := by
      unfold h_1_base
      simp only [Vector.getElem_map, ignf_init_bit]
      simp [h]
    rw [hbase]; exact le_top
/-- Monotonicity of `foldl max 0` over pointwise-bounded mapped lists. -/
lemma foldl_max_map_mono {α : Type*} (l : List α) (f g : α → ℕ) (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).foldl max 0 ≤ (l.map g).foldl max 0 := by
  suffices H : ∀ (a b : ℕ), a ≤ b → (l.map f).foldl max a ≤ (l.map g).foldl max b by
    exact H 0 0 (le_refl 0)
  induction l with
  | nil => intro a b hab; simpa using hab
  | cons x xs ih =>
    intro a b hab
    simp only [List.map_cons, List.foldl_cons]
    exact ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) _ _
      (max_le_max hab (h x (List.mem_cons_self ..)))

lemma ignf_fix_g_le {n : ℕ} (q : PlanningTask n) :
    (ignf_RN q)[(⟨n + 1, by omega⟩ : Fin (n + 2))] ≤ (ignf_extend q)[(⟨n + 1, by omega⟩ : Fin (n + 2))] := by
  set emb := Fin.castLE (show n ≤ n + 2 by omega) with hemb
  by_cases hsat : q.goal'.toList.all (fun f => ((ignf_R0 q)[f]).isSome) = true
  · have hext : (ignf_extend q)[(⟨n + 1, by omega⟩ : Fin (n + 2))]
        = some ((q.goal'.toList.map (fun f => ((ignf_R0 q)[f]).getD 0)).foldl max 0) := by
      unfold ignf_extend
      simp only [Fin.getElem_fin, Vector.getElem_ofFn]
      split_ifs with h1 h2 h3
      · exact absurd h1 (by omega)
      · exact absurd h2 (by omega)
      · rfl
      · exact absurd hsat h3
    rw [hext]
    have hRNfix : h_1_step (n+2) (i_g_normal_form q) (ignf_RN q) = ignf_RN q :=
      h_1_iter_fix_is_fixpoint (n+2) (i_g_normal_form q)
        (h_1_base (n+2) (i_g_normal_form q).init'.toBitVec)
    have hisome : ∀ g ∈ q.goal'.toList, ((ignf_R0 q)[g]).isSome := by
      intro g hg; have := List.all_eq_true.mp hsat g hg; simpa using this
    have hRNsome : ∀ g ∈ q.goal'.toList, ((ignf_RN q)[emb g]).isSome := by
      intro g hg
      have hle : (ignf_RN q)[emb g] ≤ (ignf_R0 q)[g] := ignf_fix_emb_le q g
      by_contra hcon
      rw [Option.not_isSome_iff_eq_none] at hcon
      rw [hcon, WithTop.none_eq_top, top_le_iff] at hle
      have h0 := hisome g hg
      rw [hle] at h0
      simp [← WithTop.none_eq_top] at h0
    set ga : Action (n+2) := ⟨"goal", VarSet.ofList (q.goal'.toList.map emb),
        singletonVarSet (⟨n+1, by omega⟩ : Fin (n+2)), (∅ : VarSet (n+2)), 0⟩ with hga
    have hmem : ga ∈ (i_g_normal_form q).actions' := by
      unfold i_g_normal_form; apply List.mem_append_right; simp [hga, hemb]
    have hadd : (⟨n+1, by omega⟩ : Fin (n+2)) ∈ ga.add.toList := by
      rw [hga]
      show (⟨n+1, by omega⟩ : Fin (n+2)) ∈ (singletonVarSet (⟨n+1, by omega⟩ : Fin (n+2))).toList
      rw [VarSet.toList_singletonVarSet]; simp
    have happ : applicable' ga (vec_to_state (n+2) (ignf_RN q)) = true := by
      rw [hga]
      show satisfies' (VarSet.ofList (q.goal'.toList.map emb)) (vec_to_state (n+2) (ignf_RN q)) = true
      rw [satisfies']
      simp only [decide_eq_true_eq]
      intro p hp
      rw [mem_val_ofList, List.mem_map] at hp
      obtain ⟨g, hg, rfl⟩ := hp
      rw [vec_to_state_getElem]
      exact hRNsome g hg
    have hle := fixpoint_le_actionContribUB (i_g_normal_form q) (ignf_RN q) hRNfix ga hmem
      (⟨n+1, by omega⟩) hadd happ
    have hub : actionContribUB (ignf_RN q) ga
        ≤ (q.goal'.toList.map (fun f => ((ignf_R0 q)[f]).getD 0)).foldl max 0 := by
      have hgpre : (VarSet.ofList (q.goal'.toList.map emb)).toList = q.goal'.toList.map emb :=
        VarSet.toList_ofList_sortedLT _ (toList_map_castLE_pairwise q.goal')
      simp only [hga, actionContribUB, hgpre, List.map_map, Nat.zero_add]
      apply foldl_max_map_mono
      intro g hg
      simp only [Function.comp_apply]
      exact withTop_getD_le_getD (ignf_fix_emb_le q g) (hisome g hg)
    exact le_trans hle (WithTop.coe_le_coe.mpr hub)
  · have hext : (ignf_extend q)[(⟨n + 1, by omega⟩ : Fin (n + 2))] = none := by
      unfold ignf_extend
      simp only [Fin.getElem_fin, Vector.getElem_ofFn]
      split_ifs with h1 h2 h3
      · exact absurd h1 (by omega)
      · exact absurd h2 (by omega)
      · exact absurd h3 hsat
      · rfl
    rw [hext]; exact le_top
lemma ignf_RN_eq_extend {n : ℕ} (q : PlanningTask n) :
    ignf_RN q = ignf_extend q := by
  have key : ∀ i : Fin (n+2), (ignf_RN q)[i] = (ignf_extend q)[i] := by
    intro i
    refine le_antisymm ?_ (ignf_extend_le_fix q i)
    rcases lt_trichotomy i.val n with h | h | h
    · rw [show i = Fin.castLE (show n ≤ n+2 by omega) ⟨i.val, h⟩ from Fin.ext rfl, ignf_extend_emb]
      exact ignf_fix_emb_le q ⟨i.val, h⟩
    · rw [show i = (⟨n, by omega⟩ : Fin (n+2)) from Fin.ext h, ignf_extend_i,
        show (ignf_RN q)[(⟨n, by omega⟩ : Fin (n+2))] = some 0 from ignf_fix_i q]
    · have hi : i.val = n+1 := by have := i.isLt; omega
      rw [show i = (⟨n+1, by omega⟩ : Fin (n+2)) from Fin.ext hi]
      exact ignf_fix_g_le q
  apply Vector.ext
  intro idx hidx
  exact key ⟨idx, hidx⟩
lemma ignf_fix_embed {n : ℕ} (q : PlanningTask n) (f : Fin n) :
    (ignf_RN q)[(Fin.castLE (show n ≤ n + 2 by omega) f)] = (ignf_R0 q)[f] := by
  rw [ignf_RN_eq_extend, ignf_extend_emb]

lemma ignf_fix_embed_init {n : ℕ} (q : PlanningTask n) (f : Fin n) (hf : q.init'.toBitVec[f] = true) :
    (ignf_RN q)[(Fin.castLE (show n ≤ n + 2 by omega) f)] = some 0 := by
  rw [ignf_fix_embed]; exact q_fix_init q f hf

lemma ignf_goal_foldl_eq {n : ℕ} (q : PlanningTask n)
    (h : satisfies' q.goal' (vec_to_state n (ignf_R0 q)) = true) :
    (q.goal'.toList.map (fun f => ((ignf_R0 q)[f]).getD 0)).foldl max 0 = h_1 q q.init'.toBitVec := by
  unfold h_1
  unfold ignf_R0 at h ⊢
  rw [if_pos h]
lemma h_1_le_maxFinite_of_satisfies {n : ℕ} (q : PlanningTask n)
    (h : satisfies' q.goal' (vec_to_state n (ignf_R0 q)) = true) :
    h_1 q q.init'.toBitVec ≤ Vector.maxFinite (ignf_R0 q) := by
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
  unfold satisfies'
  rw [ ignf_RN_eq_extend, ignf_extend ]
  simp 
  split_ifs <;> simp_all [ vec_to_state_getElem ]

lemma ignf_fix_goal_value {n : ℕ} (q : PlanningTask n)
    (h : satisfies' q.goal' (vec_to_state n (ignf_R0 q)) = true) :
    (ignf_RN q)[(⟨n + 1, by omega⟩ : Fin (n + 2))] = some (h_1 q q.init'.toBitVec) := by
  rw [ignf_RN_eq_extend]
  have hsat : q.goal'.toList.all (fun f => ((ignf_R0 q)[f]).isSome) = true := by
    rw [List.all_eq_true]
    intro f hf
    have hmem : f ∈ q.goal'.val := by simpa using hf
    have := (satisfies'_iff q.goal' (vec_to_state n (ignf_R0 q))).mp h f hmem
    rw [vec_to_state_getElem] at this
    simpa using this
  have hext : (ignf_extend q)[(⟨n + 1, by omega⟩ : Fin (n + 2))]
      = some ((q.goal'.toList.map (fun f => ((ignf_R0 q)[f]).getD 0)).foldl max 0) := by
    unfold ignf_extend
    simp only [Fin.getElem_fin, Vector.getElem_ofFn]
    split_ifs with h1 h2 h3
    · exact absurd h1 (by omega)
    · exact absurd h2 (by omega)
    · rfl
    · exact absurd hsat h3
  rw [hext, ignf_goal_foldl_eq q h]
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
        have h_c_eq_h1 : c = h_1 q q.init'.toBitVec := by
          have h_c_eq_h1 : R[(⟨n + 1, by omega⟩ : Fin (n + 2))] = some (h_1 q q.init'.toBitVec) := by
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
        (vec_to_state n (h_1_iter_fix n prob (h_1_base n prob.init'.toBitVec))) = true) :
    h_1 prob prob.init'.toBitVec
      = Vector.maxFinite (h_1_iter_fix n prob (h_1_base n prob.init'.toBitVec)) + 1 := by
  have := h_1_eq_maxFinite_of_not_satisfies prob prob.goal' prob.init'.toBitVec hns
  rwa [replace_goal_self] at this

lemma h_1_i_g_normal_form_eq {n : ℕ} (q : PlanningTask n) :
    h_1 (i_g_normal_form q) (i_g_normal_form q).init'.toBitVec = h_1 q q.init'.toBitVec := by
  have hgoal : (i_g_normal_form q).goal' = singletonVarSet ⟨n + 1, by omega⟩ := rfl
  by_cases h : satisfies' q.goal' (vec_to_state n (ignf_R0 q)) = true
  · have hsome : ((ignf_RN q)[(⟨n + 1, by omega⟩ : Fin (n + 2))]).isSome := by
      rw [ignf_fix_goal_isSome]; exact h
    have h1n := h_1_singleton_eq_getD (i_g_normal_form q) ⟨n + 1, by omega⟩
      (i_g_normal_form q).init'.toBitVec hsome
    rw [← hgoal, replace_goal_self] at h1n
    have hv := ignf_fix_goal_value q h
    simp only [ignf_RN] at hv
    rw [h1n, hv]; rfl
  · have hns_normal : ((ignf_RN q)[(⟨n + 1, by omega⟩ : Fin (n + 2))]).isSome = false := by
      rw [ignf_fix_goal_isSome]; rw [Bool.not_eq_true] at h; exact h
    simp only [ignf_RN] at hns_normal
    have lhs : h_1 (i_g_normal_form q) (i_g_normal_form q).init'.toBitVec
        = Vector.maxFinite (ignf_RN q) + 1 := by
      apply h_1_self_eq_maxFinite_of_not_satisfies
      rw [hgoal, satisfies'_singleton, vec_to_state_getElem, hns_normal]
      decide
    have rhs : h_1 q q.init'.toBitVec = Vector.maxFinite (ignf_R0 q) + 1 := by
      apply h_1_self_eq_maxFinite_of_not_satisfies
      simpa [ignf_R0] using h
    rw [lhs, rhs, ignf_maxFinite_eq]

/-
`h_1` does not depend on a task's initial state field (only on the state argument, actions and
goal), so overwriting the initial state is irrelevant.
-/
lemma h_1_set_init_eq {n : ℕ} (prob : PlanningTask n) (s : BitVec n) :
    h_1 (set_init prob s) s = h_1 prob s := by
  convert h_1_set_init prob s s using 1

lemma h1_goal_value_normal_form {n : ℕ} (prob : PlanningTask n) (s : BitVec n) :
    h1_goal_value (i_g_normal_form (set_init prob s))
        (get_unitary_goal (i_g_normal_form (set_init prob s))
          (i_g_normalform_is_unitary_goal _))
      = h_1 prob s := by
  have hval : get_unitary_goal (i_g_normal_form (set_init prob s))
        (i_g_normalform_is_unitary_goal _) = (⟨n + 1, by omega⟩ : Fin (n + 2)) := by
    have h := get_unitary_goal_is_goal (i_g_normal_form (set_init prob s))
      (i_g_normalform_is_unitary_goal _)
    have hgoal : (i_g_normal_form (set_init prob s)).goal'.toList
        = [(⟨n + 1, by omega⟩ : Fin (n + 2))] := by
      show (singletonVarSet (⟨n + 1, by omega⟩ : Fin (n + 2))).toList = _
      exact VarSet.toList_singletonVarSet _
    have := h.symm.trans hgoal
    simpa using this
  unfold h1_goal_value
  rw [hval]
  have hgeq : singletonVarSet (⟨n + 1, by omega⟩ : Fin (n + 2))
      = (i_g_normal_form (set_init prob s)).goal' := rfl
  rw [hgeq, replace_goal_self, h_1_i_g_normal_form_eq]
  exact h_1_set_init_eq prob s
lemma h_1_of_empty_goal {n : ℕ} (prob : PlanningTask n) (s : BitVec n) (hg : prob.goal'.toList = []) :
    h_1 prob s = 0 := by
  -- Since the goal is empty, the h_1 of the original problem is 0 by definition.
  simp [h_1, hg];
  -- Since the goal is empty, there are no elements i in the goal. Therefore, the implication holds vacuously because there are no elements to check. We can use the fact that the goal is empty to derive a contradiction.
  intro i hi
  have := hg
  simp_all 
  replace this := congr_arg List.toFinset this; rw [ Finset.ext_iff ] at this; specialize this i; aesop?

theorem lmcut_h1_dominates {n : ℕ} (prob : PlanningTask n) (s : BitVec n)
    (plan : PlanningTask.Plan prob (convertState s)) :
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
    rw [h1_goal_value_normal_form prob s] at hcore
    exact hcore

end STRIPS
