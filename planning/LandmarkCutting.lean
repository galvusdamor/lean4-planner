import planning.Landmark

namespace Validator

open List

-- The `i_g_normal_form` construction unfolds to a sizable `STRIPS`, so some proofs about it need a
-- larger elaboration budget than the default.
set_option maxHeartbeats 1000000

/-- Mapping a strictly sorted list of variables along the order embedding `Fin.castLE`
keeps it strictly sorted. -/
private lemma sortedLT_map_castLE {n m : ℕ} (h : n ≤ m) {l : List (Fin n)}
    (hl : l.SortedLT) : (l.map (Fin.castLE h)).SortedLT := by
  grind

/-- Appending a variable that is strictly larger than every element of a strictly sorted list
keeps the list strictly sorted. -/
private lemma sortedLT_append_top {m : ℕ} {l : List (Fin m)} {t : Fin m}
    (hl : l.SortedLT) (ht : ∀ x ∈ l, x < t) : (l ++ [t]).SortedLT := by
  grind

def i_g_normal_form {n : ℕ} (prob : STRIPS n) : STRIPS (n+2) :=
  let emb : Fin n → Fin (n + 2) := Fin.castLE (by omega)
  let goal_pre : VarSet' (n + 2) :=
       ⟨ prob.goal'.val.map emb, sortedLT_map_castLE (by omega) prob.goal'.property⟩
       -- the current goal is the precondition of the goal action

  STRIPS.mk
    (prob.varNames.append (⟨#["i","g"] , by rfl⟩))
    ((prob.actions'.map (fun a =>
      Action.mk  a.name
        ⟨ (a.pre'.val.map emb) ++ [⟨n, by omega⟩],
          sortedLT_append_top (sortedLT_map_castLE (by omega) a.pre'.property)
            (by
              intro x hx
              simp only [List.mem_map] at hx
              obtain ⟨y, _, rfl⟩ := hx
              simpa only [Fin.lt_def, Fin.val_castLE] using y.isLt)⟩
          -- every action gets n as an additional precondition
        ⟨ a.add'.val.map emb, sortedLT_map_castLE (by omega) a.add'.property⟩
        ⟨ a.del'.val.map emb, sortedLT_map_castLE (by omega) a.del'.property⟩
        a.cost
      )) ++
      [Action.mk
        "init"
        (⟨[⟨ n, by simp⟩ ], by grind⟩) -- pre is only init
        -- Corrected `add` effect.  The original
        --   `varset'_of_state' ((prob.init'.concat false).concat false)`
        -- is buggy: `BitVec.concat` shifts the bits **up**, so it would place the initial facts at
        -- positions `2 .. n+1` whereas the original variables are embedded (via `emb = Fin.castLE`)
        -- at positions `0 .. n-1`.  Hence the `init` action would never establish the embedded
        -- initial facts, breaking `i_g_normal_form_keeps_h_plus`.  We instead add exactly the
        -- embedded initial facts.
        (⟨(varset'_of_state' prob.init').val.map emb,
            sortedLT_map_castLE (by omega) (varset'_of_state' prob.init').property⟩)
        ⟨[],by apply List.sortedLT_iff_pairwise.mpr ; simp⟩ -- no deletes
        0,
        Action.mk
        "goal"
        goal_pre
        (⟨[⟨ n+1, by simp⟩ ], by grind⟩) -- add is only goal
        ⟨[],by apply List.sortedLT_iff_pairwise.mpr ; simp⟩ -- no deletes
        0
      ]
    )
    (BitVec.zero (n+2) ||| (BitVec.twoPow (n+2) (n))) -- the initial state now contains only i
    (⟨[⟨ n+1, by simp⟩ ], by grind⟩) -- only g is now a goal

/-- The cost of a concatenation of paths is the sum of the costs. -/
private lemma Path.cost_append {n : ℕ} {pt : STRIPS n} {a b c : State n}
    (p : Path pt a b) (q : Path pt b c) : (p.append q).cost = p.cost + q.cost := by
  induction p <;> simp_all +decide [ Path.append ];
  · rfl;
  · simp_all +decide [ Path.cost ];
    ring

/--
In a delete relaxation every action has an empty delete effect.
-/
private lemma dr_action_del_empty {n : ℕ} (X : STRIPS n) {a : Action n}
    (ha : a ∈ (delete_relaxation X).actions) : a.del = ∅ := by
  unfold delete_relaxation at ha; simp_all +decide [ STRIPS.actions ] ;
  obtain ⟨ b, hb, rfl ⟩ := ha; unfold delete_relax_action; simp +decide [ Action.del ] ;
  unfold convertVarSet; simp +decide ;

/--
The cross-dimensional lifting at the heart of the forward direction.  An original delete-relaxed
path can be replayed in the normal form whenever the start state embeds (with the auxiliary `i`
variable present), using the embedded original actions, with the same cost.
-/
private lemma lift_forward {n : ℕ} (prob : STRIPS n) {S1 S2 : State n}
    (p : Path (delete_relaxation prob) S1 S2)
    {T0 : State (n + 2)}
    (hi : (⟨n, by omega⟩ : Fin (n + 2)) ∈ T0)
    (hsub : ∀ x ∈ S1, (Fin.castLE (show n ≤ n + 2 by omega) x) ∈ T0) :
    ∃ T2 : State (n + 2),
      (⟨n, by omega⟩ : Fin (n + 2)) ∈ T2 ∧
      (∀ x ∈ S2, (Fin.castLE (show n ≤ n + 2 by omega) x) ∈ T2) ∧
      ∃ q : Path (delete_relaxation (i_g_normal_form prob)) T0 T2, q.cost = p.cost := by
  induction' p with a s2 s3 ha succ p ih generalizing T0;
  · exact ⟨ T0, hi, hsub, Path.empty T0, rfl ⟩;
  · obtain ⟨a, ha_mem, ha_eq⟩ : ∃ a ∈ prob.actions', s2 = delete_relax_action a := by
      unfold delete_relaxation at p; simp_all +decide [ STRIPS.actions ] ;
      grind;
    -- Define the embedded action `e` in the normal form.
    set e : Action (n + 2) := delete_relax_action (Action.mk a.name ⟨a.pre'.val.map (Fin.castLE (by omega)) ++ [⟨n, by omega⟩], sortedLT_append_top (sortedLT_map_castLE (by omega) a.pre'.property) (by
      intro x hx
      simp only [mem_map] at hx
      obtain ⟨y, _, rfl⟩ := hx
      simpa only [Fin.lt_def, Fin.val_castLE] using y.isLt)⟩ ⟨a.add'.val.map (Fin.castLE (by omega)), sortedLT_map_castLE (by omega) a.add'.property⟩ ⟨a.del'.val.map (Fin.castLE (by omega)), sortedLT_map_castLE (by omega) a.del'.property⟩ a.cost);
    -- Show that `e` is in the actions of the delete-relaxed normal form.
    have he_mem : e ∈ (delete_relaxation (i_g_normal_form prob)).actions := by
      unfold delete_relaxation i_g_normal_form; simp +decide [ STRIPS.actions, List.mem_map ] ;
      exact Or.inr <| Or.inr <| ⟨ a, ha_mem, rfl ⟩;
    have he_pre : e.pre ⊆ T0 := by
      intro x hx;
      unfold e at hx; simp_all +decide [ delete_relax_action, Action.pre ] ;
      unfold convertVarSet at hx; simp_all +decide ;
      rcases hx with ( rfl | ⟨ y, hy, rfl ⟩ ) <;> [ exact hi; exact hsub y ( by
        exact ih.1 ( by unfold Action.pre; unfold convertVarSet; simp +decide ; aesop ) ) ];
    have he_succ : Successor e T0 (T0 ∪ e.add) := by
      refine ⟨he_pre, ?_⟩
      rw [show e.del = ∅ from dr_action_del_empty _ he_mem, Set.diff_empty]
    rename_i h;
    obtain ⟨ T2, hT2₁, hT2₂, q, hq ⟩ := h ( show ⟨ n, by omega ⟩ ∈ T0 ∪ e.add from by
                                              grind ) ( show ∀ x ∈ ha, Fin.castLE ( by omega ) x ∈ T0 ∪ e.add from by
                                                                                                  intro x hx; specialize ih; cases ih; simp_all +decide [ Successor ] ;
                                                                                                  unfold e; simp +decide [ delete_relax_action ] ;
                                                                                                  unfold delete_relax_action at hx; simp_all +decide [ Action.del, Action.add ] ;
                                                                                                  unfold convertVarSet at *; simp_all +decide ;
                                                                                                  grind );
    use T2, hT2₁, hT2₂, Path.cons e (T0 ∪ e.add) (by
    exact he_mem) (by
    exact he_succ) q;
    simp +decide [ *, Path.cost ];
    unfold e; simp +decide [ delete_relax_action ] ;

/--
Forward direction: a delete-relaxed plan of the original task gives a delete-relaxed plan of the
i/g normal form with the *same* cost.  Replay the original plan after the (free) `init` action and
close it with the (free) `goal` action; the auxiliary variable `i` is supplied by `init` and never
deleted, so every original action stays applicable.
-/
private lemma ignf_dr_plan_of_dr_plan {n : ℕ} (prob : STRIPS n)
    (plan : Plan (delete_relaxation prob) (delete_relaxation prob).init) :
    ∃ eplan : Plan (delete_relaxation (i_g_normal_form prob))
        (delete_relaxation (i_g_normal_form prob)).init,
      eplan.path.cost = plan.path.cost := by
  revert plan;
  intro plan
  obtain ⟨last, p, hgoal⟩ := plan
  have h_init : (delete_relaxation (i_g_normal_form prob)).init = {y | y = (⟨n, by omega⟩ : Fin (n + 2))} := by
    unfold delete_relaxation i_g_normal_form; simp +decide [ STRIPS.init ] ;
    ext ⟨x, hx⟩; simp [convertState, BitVec.getElem_twoPow];
  obtain ⟨T0, hT0⟩ : ∃ T0 : State (n + 2), (⟨n, by omega⟩ : Fin (n + 2)) ∈ T0 ∧ (∀ x ∈ (delete_relaxation prob).init, (Fin.castLE (show n ≤ n + 2 by omega) x) ∈ T0) ∧ ∃ q : Path (delete_relaxation (i_g_normal_form prob)) (delete_relaxation (i_g_normal_form prob)).init T0, q.cost = 0 := by
                                                                                                                                    use {y | y = (⟨n, by omega⟩ : Fin (n + 2))} ∪ (delete_relaxation prob).init.image (Fin.castLE (show n ≤ n + 2 by omega));
                                                                                                                                    refine' ⟨ _, _, _ ⟩;
                                                                                                                                    · exact Set.mem_union_left _ rfl;
                                                                                                                                    · exact fun x hx => Or.inr ⟨ x, hx, rfl ⟩;
                                                                                                                                    · constructor;
                                                                                                                                      swap;
                                                                                                                                      refine' Path.cons _ _ _ _ ( Path.empty _ );
                                                                                                                                      exact delete_relax_action ( Action.mk "init" ⟨ [ ⟨ n, by omega ⟩ ], by grind ⟩ ⟨ ( varset'_of_state' prob.init' ).val.map ( Fin.castLE ( by omega ) ), sortedLT_map_castLE ( by omega ) ( varset'_of_state' prob.init' ).property ⟩ ⟨ [ ], by apply List.sortedLT_iff_pairwise.mpr ; simp ⟩ 0 );
                                                                                                                                      all_goals norm_num [ delete_relax_action, Successor ];
                                                                                                                                      all_goals norm_num [ Applicable, Successor, Path.cost ];
                                                                                                                                      · unfold delete_relaxation i_g_normal_form; simp +decide [ STRIPS.actions, List.mem_map ] ;
                                                                                                                                        exact Or.inl rfl;
                                                                                                                                      · simp +decide [ Set.subset_def, Set.ext_iff ];
                                                                                                                                        simp +decide [ h_init, Action.pre, Action.add, Action.del ];
                                                                                                                                        simp +decide [ convertVarSet, varset'_of_state' ];
                                                                                                                                        simp +decide [ delete_relaxation, STRIPS.init, convertState ];
  obtain ⟨T2, hT2₁, hT2₂, q, hq⟩ := lift_forward prob p hT0.left hT0.right.left;
  -- Construct the goal step
  obtain ⟨aG, haG⟩ : ∃ aG : Action (n + 2), aG ∈ (delete_relaxation (i_g_normal_form prob)).actions ∧ aG.pre ⊆ T2 ∧ aG.del = ∅ ∧ aG.cost = 0 ∧ aG.add = {⟨n + 1, by omega⟩} := by
    unfold delete_relaxation i_g_normal_form; simp +decide [ STRIPS.actions, List.mem_map ] ;
    refine Or.inr <| Or.inl ⟨ ?_, ?_, ?_, ?_ ⟩ <;> simp +decide [ delete_relax_action ];
    · intro x hx; unfold Action.pre at hx; unfold convertVarSet at hx; simp_all +decide ;
      obtain ⟨ a, ha, rfl ⟩ := hx; exact hT2₂ a ( hgoal ( by unfold convertVarSet; simp +decide ; aesop ) ) ;
    · unfold Action.del; simp +decide [ convertVarSet ] ;
    · unfold Action.add; simp +decide [ convertVarSet ] ;
  obtain ⟨q', hq'⟩ : ∃ q' : Path (delete_relaxation (i_g_normal_form prob)) T2 (T2 ∪ aG.add), q'.cost = 0 := by
    use Path.cons aG (T2 ∪ aG.add) haG.left (by
    unfold Successor; aesop;) (Path.empty (T2 ∪ aG.add))
    generalize_proofs at *;
    simp +decide [ Path.cost, haG ];
  use ⟨T2 ∪ aG.add, (hT0.right.right.choose.append q).append q', by
    unfold delete_relaxation i_g_normal_form at *; simp_all +decide [ STRIPS.GoalState, convertVarSet ] ;⟩
  simp only [Path.cost_append, hT0.right.right.choose_spec, hq, hq', Nat.zero_add, Nat.add_zero]

/--
Delete-relaxed paths are monotone: facts are only ever added.
-/
private lemma dr_path_mono {n : ℕ} {pt : STRIPS n} (hdel : ∀ a ∈ pt.actions, a.del = ∅)
    {s1 s2 : State n} (p : Path pt s1 s2) : s1 ⊆ s2 := by
  induction p;
  · exact Set.Subset.refl _;
  · grind

/--
If the auxiliary goal variable `g` becomes true along a normal-form delete-relaxed path that did
not start with `g`, then the embedded original goal facts are all true at the end (the only action
that can add `g` is the `goal` action, whose precondition is exactly the embedded goal).
-/
private lemma ep_goal_facts {n : ℕ} (prob : STRIPS n) {E1 E2 : State (n + 2)}
    (q : Path (delete_relaxation (i_g_normal_form prob)) E1 E2)
    (h1 : (⟨n + 1, by omega⟩ : Fin (n + 2)) ∉ E1)
    (h2 : (⟨n + 1, by omega⟩ : Fin (n + 2)) ∈ E2) :
    ∀ x ∈ convertVarSet prob.goal', (Fin.castLE (show n ≤ n + 2 by omega) x) ∈ E2 := by
  induction q;
  · tauto;
  · rename_i a s1 s2 s3 ha succ π ih;
    by_cases h : ⟨n + 1, by omega⟩ ∈ s2 <;> simp_all +decide [ Successor ];
    unfold delete_relaxation i_g_normal_form at ha; simp_all +decide [ STRIPS.actions, List.mem_map ] ;
    rcases ha with ( rfl | rfl | ⟨ a, ha, rfl ⟩ ) <;> simp_all +decide [ delete_relax_action, Action.add ];
    · unfold convertVarSet at h; simp_all +decide ;
      obtain ⟨ a, ha, ha' ⟩ := h; replace ha' := congr_arg Fin.val ha'; simp_all +decide ;
      grind;
    · have := dr_path_mono ( show ∀ a ∈ ( delete_relaxation ( i_g_normal_form prob ) ).actions, a.del = ∅ from fun a ha => dr_action_del_empty _ ha ) π; simp_all +decide [ Set.subset_def ] ;
      simp_all +decide [ Action.pre, Action.del ];
      unfold convertVarSet at *; simp_all +decide ;
    · unfold convertVarSet at h; simp_all +decide ;
      obtain ⟨ x, hx, hx' ⟩ := h; have := Fin.is_lt x; simp_all +decide [ Fin.ext_iff ] ;

/--
Projecting `Fin.castLE`-embedded membership back: `emb x` lies in the image list iff `x` lies in
the original list (`Fin.castLE` is injective).
-/
private lemma castLE_mem_map_castLE {n m : ℕ} (h : n ≤ m) (l : List (Fin n)) (x : Fin n) :
    (Fin.castLE h x) ∈ (l.map (Fin.castLE h)).toFinset ↔ x ∈ l.toFinset := by
  aesop

/--
Prepending a projected original action to an original delete-relaxed path.
-/
private lemma project_cons_embedded {n : ℕ} (prob : STRIPS n) {a : Action n}
    (ha : a ∈ prob.actions') {D0 F : State n} (hpre : a.pre ⊆ D0)
    (dq : Path (delete_relaxation prob) (D0 ∪ a.add) F) :
    ∃ dq' : Path (delete_relaxation prob) D0 F, dq'.cost = dq.cost + a.cost := by
  use Path.cons (delete_relax_action a) (D0 ∪ a.add) (by
  unfold delete_relaxation; simp +decide [ STRIPS.actions, List.mem_map ] ;
  grind) (by
  unfold Successor; simp_all +decide [ delete_relax_action, Action.pre, Action.add, Action.del ] ;
  unfold convertVarSet at *; simp_all +decide ;
  exact fun x hx => hpre <| by unfold Action.pre at hx; unfold convertVarSet at hx; simp_all +decide ;) dq
  generalize_proofs at *;
  simp +decide [ Path.cost, delete_relax_action ]

/-- The projection at the heart of the backward direction.  Projecting a normal-form delete-relaxed
path to the original variables, starting from any original state `D0` that already contains the
original initial state and the projection of the start state, yields an original delete-relaxed path
of no greater cost reaching `D0` together with the projection of the end state. -/
private lemma project_backward {n : ℕ} (prob : STRIPS n) {E1 E2 : State (n + 2)}
    (q : Path (delete_relaxation (i_g_normal_form prob)) E1 E2)
    {D0 : State n}
    (hD : convertState prob.init' ⊆ D0)
    (hD0 : {x : Fin n | (Fin.castLE (show n ≤ n + 2 by omega) x) ∈ E1} ⊆ D0) :
    ∃ dq : Path (delete_relaxation prob) D0
        (D0 ∪ {x : Fin n | (Fin.castLE (show n ≤ n + 2 by omega) x) ∈ E2}),
      dq.cost ≤ q.cost := by
  induction q generalizing D0 with
  | empty s =>
    rw [Set.union_eq_left.mpr hD0]
    exact ⟨Path.empty D0, by simp [Path.cost]⟩
  | cons a' s2 ha' succ' rest ih =>
    rename_i Estart Eend
    obtain ⟨b, hb, hbeq⟩ : ∃ b ∈ (i_g_normal_form prob).actions', delete_relax_action b = a' := by
      have h2 : a' ∈ ((i_g_normal_form prob).actions'.map delete_relax_action).toFinset := ha'
      rw [List.mem_toFinset, List.mem_map] at h2
      exact h2
    subst hbeq
    have hpre' : (delete_relax_action b).pre ⊆ Estart := succ'.1
    have hs2 : s2 = Estart ∪ (delete_relax_action b).add := by
      have h := succ'.2; rwa [dr_action_del_empty _ ha', Set.diff_empty] at h
    have hmono : s2 ⊆ Eend := dr_path_mono (fun c hc => dr_action_del_empty _ hc) rest
    have hcons_cost : (Path.cons (delete_relax_action b) s2 ha' succ' rest).cost
        = rest.cost + (delete_relax_action b).cost := rfl
    have hEstart_sub : {x : Fin n | (Fin.castLE (show n ≤ n + 2 by omega) x) ∈ Estart} ⊆ D0 := hD0
    simp only [i_g_normal_form, List.mem_append, List.mem_map, List.mem_cons,
      List.not_mem_nil, or_false] at hb
    obtain ⟨a, ha, rfl⟩ | rfl | rfl := hb
    · -- embedded action `b = embedded a`
      have hsub2 : {x : Fin n | (Fin.castLE (show n ≤ n + 2 by omega) x) ∈ s2} ⊆ D0 ∪ a.add := by
        intro x hx
        simp only [Set.mem_setOf_eq] at hx
        simp only [hs2, Set.mem_union, delete_relax_action, Action.add, convertVarSet,
          Finset.mem_coe, List.mem_toFinset, List.mem_map] at hx
        rcases hx with hx | ⟨y, hy, hyx⟩
        · exact Or.inl (hEstart_sub hx)
        · have hyx' : y = x :=
            Fin.ext (by have := congrArg Fin.val hyx; simpa [Fin.val_castLE] using this)
          subst hyx'
          refine Or.inr ?_
          rw [Action.add, convertVarSet, Finset.mem_coe, List.mem_toFinset]; exact hy
      have hpreD0 : a.pre ⊆ D0 := by
        intro y hy
        apply hD0
        apply hpre'
        simp only [delete_relax_action, Action.pre, convertVarSet, Finset.mem_coe,
          List.mem_toFinset, List.mem_append, List.mem_map, List.mem_singleton]
        refine Or.inl ⟨y, ?_, rfl⟩
        rw [Action.pre, convertVarSet, Finset.mem_coe, List.mem_toFinset] at hy
        exact hy
      obtain ⟨dq_rest, hdq_rest⟩ := ih (D0 := D0 ∪ a.add)
        (Set.Subset.trans hD Set.subset_union_left) hsub2
      obtain ⟨dq', hdq'⟩ := project_cons_embedded prob ha hpreD0 dq_rest
      have haS : a.add ⊆ {x : Fin n | (Fin.castLE (show n ≤ n + 2 by omega) x) ∈ Eend} := by
        intro x hx
        apply hmono
        simp only [hs2, Set.mem_union]
        refine Or.inr ?_
        simp only [delete_relax_action, Action.add, convertVarSet, Finset.mem_coe,
          List.mem_toFinset, List.mem_map]
        rw [Action.add, convertVarSet, Finset.mem_coe, List.mem_toFinset] at hx
        exact ⟨x, hx, rfl⟩
      have key : (D0 ∪ a.add) ∪ {x : Fin n | (Fin.castLE (show n ≤ n + 2 by omega) x) ∈ Eend}
          = D0 ∪ {x : Fin n | (Fin.castLE (show n ≤ n + 2 by omega) x) ∈ Eend} := by
        rw [Set.union_assoc, Set.union_eq_right.mpr haS]
      rw [← key]
      exact ⟨dq', by rw [hdq']; exact Nat.add_le_add_right hdq_rest _⟩
    · -- init action
      have hsub2 : {x : Fin n | (Fin.castLE (show n ≤ n + 2 by omega) x) ∈ s2} ⊆ D0 := by
        intro x hx
        simp only [Set.mem_setOf_eq] at hx
        simp only [hs2, Set.mem_union, delete_relax_action, Action.add, convertVarSet,
          Finset.mem_coe, List.mem_toFinset, List.mem_map] at hx
        rcases hx with hx | ⟨y, hy, hyx⟩
        · exact hEstart_sub hx
        · have hyx' : y = x :=
            Fin.ext (by have := congrArg Fin.val hyx; simpa [Fin.val_castLE] using this)
          subst hyx'
          apply hD
          rw [varset'_of_state'_mem] at hy
          simpa [convertState] using hy
      obtain ⟨dq, hdq⟩ := ih hD hsub2
      exact ⟨dq, by rw [hcons_cost]; exact hdq.trans (Nat.le_add_right _ _)⟩
    · -- goal action
      have hsub2 : {x : Fin n | (Fin.castLE (show n ≤ n + 2 by omega) x) ∈ s2} ⊆ D0 := by
        intro x hx
        simp only [Set.mem_setOf_eq] at hx
        simp only [hs2, Set.mem_union, delete_relax_action, Action.add, convertVarSet,
          Finset.mem_coe, List.mem_toFinset, List.mem_singleton] at hx
        rcases hx with hx | hx
        · exact hEstart_sub hx
        · exfalso
          have hlt := x.isLt
          have := congrArg Fin.val hx
          simp only [Fin.val_castLE] at this
          omega
      obtain ⟨dq, hdq⟩ := ih hD hsub2
      exact ⟨dq, by rw [hcons_cost]; exact hdq.trans (Nat.le_add_right _ _)⟩

/-- Backward direction: a delete-relaxed plan of the i/g normal form gives a delete-relaxed plan of
the original task whose cost is no larger.  Drop the `init`/`goal` actions (both of cost `0`) and
project the remaining actions back to the original task. -/
private lemma dr_plan_of_ignf_dr_plan {n : ℕ} (prob : STRIPS n)
    (eplan : Plan (delete_relaxation (i_g_normal_form prob))
        (delete_relaxation (i_g_normal_form prob)).init) :
    ∃ plan : Plan (delete_relaxation prob) (delete_relaxation prob).init,
      plan.path.cost ≤ eplan.path.cost := by
  obtain ⟨elast, ep_p, ehgoal⟩ := eplan
  have h_init : (delete_relaxation (i_g_normal_form prob)).init
      = {y : Fin (n + 2) | y = ⟨n, by omega⟩} := by
    unfold delete_relaxation i_g_normal_form
    simp only [STRIPS.init]
    ext ⟨x, hx⟩
    simp [convertState, BitVec.getElem_twoPow]
  have hD0 : {x : Fin n | (Fin.castLE (show n ≤ n + 2 by omega) x)
      ∈ (delete_relaxation (i_g_normal_form prob)).init} ⊆ convertState prob.init' := by
    intro x hx
    rw [h_init] at hx
    simp only [Set.mem_setOf_eq] at hx
    have hval := congrArg Fin.val hx
    simp only [Fin.val_castLE] at hval
    have := x.isLt; omega
  obtain ⟨dq, hdq⟩ := project_backward prob ep_p (Set.Subset.refl _) hD0
  have hg_notin : (⟨n + 1, by omega⟩ : Fin (n + 2))
      ∉ (delete_relaxation (i_g_normal_form prob)).init := by
    rw [h_init]; simp [Fin.ext_iff]
  have hg_in : (⟨n + 1, by omega⟩ : Fin (n + 2)) ∈ elast := by
    apply ehgoal
    unfold delete_relaxation i_g_normal_form
    simp [convertVarSet]
  have hgoalfacts := ep_goal_facts prob ep_p hg_notin hg_in
  refine ⟨⟨convertState prob.init'
      ∪ {x : Fin n | (Fin.castLE (show n ≤ n + 2 by omega) x) ∈ elast}, dq, ?_⟩, hdq⟩
  intro z hz
  exact Set.mem_union_right _ (hgoalfacts z hz)

/-- `i_g_normal_form` preserves `h_plus`, **provided** the delete relaxation of `prob` is solvable
from its initial state.

The solvability hypothesis is necessary: the original unconditional statement
`h_plus prob prob.init' = h_plus (i_g_normal_form prob) (i_g_normal_form prob).init'`
is **false**.  When the delete relaxation is unsolvable, `h_plus` returns the sentinel
`2 ^ k * max_action_cost`, but the two sides are evaluated in different dimensions, `k = n` on the
left and `k = n + 2` on the right, so they disagree by a factor of `4` (and `max_action_cost` may
differ as well).  Concretely, for `n = 1` with no actions, initial variable `false`, and a goal
requiring that variable to be `true`, one computes `h_plus prob prob.init' = 2` while
`h_plus (i_g_normal_form prob) _ = 0`. -/
lemma i_g_normal_form_keeps_h_plus {n : ℕ} {prob : STRIPS n}
    (hsolv : ¬ Unsolvable (delete_relaxation prob)) :
   h_plus prob prob.init' = h_plus (i_g_normal_form prob) (i_g_normal_form prob).init'  := by
     obtain ⟨dplan⟩ : Nonempty (Plan (delete_relaxation prob) (delete_relaxation prob).init) := by
       contrapose! hsolv; aesop;
     -- Let `rdp := (planner dp (fun _ => 0)).get hdp` and `rep := (planner ep (fun _ => 0)).get hep`.
     obtain ⟨rdp, hrdp⟩ : ∃ rdp, (Validator.planner (Validator.delete_relaxation prob) (fun _ => 0)) = some rdp := by
       exact Option.isSome_iff_exists.mp ( by exact Option.isSome_iff_ne_none.mpr fun h => hsolv <| Validator.planner_complete _ _ h )
     obtain ⟨rep, hrep⟩ : ∃ rep, (Validator.planner (Validator.delete_relaxation (i_g_normal_form prob)) (fun _ => 0)) = some rep := by
       obtain ⟨eplan, heplan⟩ : ∃ eplan : Plan (delete_relaxation (i_g_normal_form prob)) (delete_relaxation (i_g_normal_form prob)).init, True := by
         exact ⟨ ignf_dr_plan_of_dr_plan prob dplan |> Classical.choose, trivial ⟩;
       have := planner_complete ( delete_relaxation ( i_g_normal_form prob ) ) ( fun _ => 0 ) ; simp_all +decide [ Unsolvable ] ;
       cases h : planner ( delete_relaxation ( i_g_normal_form prob ) ) ( fun x => 0 ) <;> simp_all +decide [ UnsolvableState ];
       exact this.elim eplan;
     obtain ⟨eplan, heplan⟩ : ∃ eplan, (Validator.planner (Validator.delete_relaxation (i_g_normal_form prob)) (fun _ => 0)) = some eplan ∧ eplan.path.cost ≤ rdp.path.cost := by
       obtain ⟨eplan, heplan⟩ : ∃ eplan, (Validator.planner (Validator.delete_relaxation (i_g_normal_form prob)) (fun _ => 0)) = some eplan ∧ eplan.path.cost ≤ rdp.path.cost := by
         have := ignf_dr_plan_of_dr_plan prob rdp
         obtain ⟨eplan, heplan⟩ := this
         have := Validator.planner_optimal (Validator.delete_relaxation (Validator.i_g_normal_form prob)) (fun _ => 0) (Validator.zero_heur_admissible (Validator.delete_relaxation (Validator.i_g_normal_form prob))) (by
         exact hrep.symm ▸ rfl) eplan
         generalize_proofs at *;
         grind;
       use eplan;
     obtain ⟨plan, hplan⟩ : ∃ plan, (Validator.planner (Validator.delete_relaxation prob) (fun _ => 0)) = some plan ∧ plan.path.cost ≤ rep.path.cost := by
       obtain ⟨plan, hplan⟩ : ∃ plan : Plan (Validator.delete_relaxation prob) (Validator.delete_relaxation prob).init, plan.path.cost ≤ rep.path.cost := by
         exact ⟨ _, dr_plan_of_ignf_dr_plan prob rep |> Classical.choose_spec ⟩;
       have := Validator.planner_optimal ( Validator.delete_relaxation prob ) ( fun _ => 0 ) ( Validator.zero_heur_admissible ( Validator.delete_relaxation prob ) ) ( show ( Validator.planner ( Validator.delete_relaxation prob ) ( fun _ => 0 ) ).isSome from by
                                                                                                                                                                         grind ) plan;
       grind;
     unfold h_plus;
     simp_all +decide [ delete_relaxation ];
     grind


/- Theory of PCFs and justification graphs -/

/-- should be a type of functions that take an action from prob and return one of their preconditions -/
abbrev precondition_choice_function {n : ℕ} (prob : STRIPS n):=
    Π (a : {b : Action n // b ∈ prob.actions'}), { p : Fin n // p ∈ a.val.pre}


