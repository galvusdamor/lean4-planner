import planning.Landmark
import planning.CostPartitioning

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

lemma i_g_normal_form_keeps_solvability {n : ℕ} {prob : STRIPS n} : 
    Unsolvable (delete_relaxation prob) ↔
      Unsolvable (delete_relaxation ((i_g_normal_form prob))) := by
  constructor <;> intro h
  · -- A delete-relaxed plan of the normal form would project back to one of the original task.
    exact ⟨fun eplan => h.false (dr_plan_of_ignf_dr_plan prob eplan).choose⟩
  · -- A delete-relaxed plan of the original task lifts to one of the normal form.
    exact ⟨fun plan => h.false (ignf_dr_plan_of_dr_plan prob plan).choose⟩


/- Theory of PCFs and justification graphs -/

/-- should be a type of functions that take an action from prob and return one of their preconditions -/
abbrev precondition_choice_function {n : ℕ} (prob : STRIPS n):=
    Π (a : {b : Action n // b ∈ prob.actions'}), { p : Fin n // p ∈ a.val.pre}



/-- the IG normalform has only one init fact and one goal fact and we are able to obtain them -/

def unitary_init {n : ℕ} (prob : STRIPS n) : Prop := prob.init.ncard == 1
def unitary_goal {n : ℕ} (prob : STRIPS n) : Prop := prob.goal'.val.length == 1
/-- In the i/g normal form the only initial fact is the auxiliary variable `i` (at index `n`). -/
lemma i_g_normalform_init_eq {n : ℕ} (prob : STRIPS n) :
    (i_g_normal_form prob).init = {(⟨n, by omega⟩ : Fin (n + 2))} := by
  unfold STRIPS.init i_g_normal_form
  ext ⟨x, hx⟩
  simp [convertState, BitVec.getElem_twoPow]

lemma i_g_normalform_is_unitary_init {n : ℕ} (prob : STRIPS n):
    unitary_init (i_g_normal_form prob) := by
  rw [unitary_init, beq_iff_eq, i_g_normalform_init_eq, Set.ncard_singleton]
lemma i_g_normalform_is_unitary_goal {n : ℕ} (prob : STRIPS n):
    unitary_goal (i_g_normal_form prob) := by
  rfl


noncomputable def get_unitary_init {n : ℕ} (prob : STRIPS n) (u : unitary_init prob) : Fin n :=
  (Set.ncard_eq_one.mp (by
    have := u; simp only [unitary_init, beq_iff_eq] at this; exact this)).choose

def get_unitary_goal{n : ℕ} (prob : STRIPS n) (u : unitary_goal prob) : Fin n :=
  prob.goal'.val.head (by unfold unitary_goal at u ; grind)

lemma get_unitary_init_is_init {n : ℕ} (prob : STRIPS n) (u : unitary_init prob):
    prob.init = {get_unitary_init prob u} :=
  (Set.ncard_eq_one.mp (by
    have := u; simp only [unitary_init, beq_iff_eq] at this; exact this)).choose_spec

lemma get_unitary_goal_is_goal {n : ℕ} (prob : STRIPS n) (u : unitary_goal prob):
    prob.goal'.val = [get_unitary_goal prob u] := by
  have hlen : prob.goal'.val.length = 1 := by
    have := u; simp only [unitary_goal, beq_iff_eq] at this; exact this
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hlen
  simp [get_unitary_goal, ha]



/-- the justification graph selects one precodnition per action and connects facts using them - and ignoring their deleting effects. We use NatGraph here for now, as we have search algorithms for them -/
def justification_graph {n : ℕ} (prob : STRIPS n) (pcf : precondition_choice_function prob) : NatGraph (Fin n) := 
  -- We quantify over the subtype `{b // b ∈ prob.actions'}` so that the precondition choice
  -- function `pcf` can be applied directly (it needs the membership witness), avoiding the
  -- previous `by sorry`.  Membership is phrased through `a.val.add'.val.toFinset`, which is
  -- definitionally `t ∈ a.val.add`, so that the relation is decidable.
  let edges : Fin n → Fin n → Prop := fun f t => 
    ∃ a : {b : Action n // b ∈ prob.actions'}, f = (↑(pcf a) : Fin n) ∧ t ∈ a.val.add'.val.toFinset

  let dg : Digraph (Fin n) := Digraph.mk edges
  let dg_dec : DecidableRel dg.Adj := fun f t => inferInstanceAs (Decidable (edges f t))

  -- cost of an edge is the cheapest cost of an action that created that edge
  let cost : (u v : Fin n) → dg.Adj u v → ℕ := fun f t adj =>
    let edgeActions : List (Action n) := prob.actions'.filter (fun a =>
      f = (↑(pcf a) : Fin n) ∧ t ∈ a.val.add'.val.toFinset)
    (edgeActions.map (·.cost)).min (by sorry)

  WeightedDiGraph.mk dg cost dg_dec


def remove_edges {V : Type} {E : Type} [FinEnum V] (g : WeightedDiGraph V E) (cut : List (V × V)) : WeightedDiGraph V E :=
  let edges : V → V → Prop := fun f t => (g.Adj f t) ∧ (f,t) ∉ cut    

  let dg : Digraph V := Digraph.mk edges
  let dg_dec : DecidableRel dg.Adj := fun f t =>
    haveI := g.instDecAdj f t
    inferInstanceAs (Decidable (g.Adj f t ∧ (f,t) ∉ cut))
  -- The surviving edges are exactly those of `g` that were not cut, so the payload of `g` still
  -- applies; the adjacency proof `adj.1` provides the original edge.
  let cost : (u v : V) → dg.Adj u v → E := fun f t adj => g.Payload f t adj.1

  WeightedDiGraph.mk dg cost dg_dec



/-- a cut is a set of edges that if removed ensure that no path exists between s and t -/
abbrev cut_in_graph {V : Type} {E : Type}  [FinEnum V] (g : WeightedDiGraph V E) (s t : V) (cut : List (V × V)) := 
  IsEmpty ((remove_edges g cut).Path s t)


def landmark_induced_by_cut {n : ℕ} (prob : STRIPS n) (cut : List (Fin n × Fin n)) (pcf : precondition_choice_function prob) : List (Action n) :=
    cut.flatMap (fun (f,t) => (prob.actions'.attach.filter (fun a =>
      decide (f = (↑(pcf a) : Fin n) ∧ t ∈ a.val.add'.val.toFinset)
    )).map (·.val) )


/-- Core reachability lemma for the cut argument.  Replaying a delete-relaxed path of `prob`,
every fact that is true at the end of the path can be reached, in the *cut* justification graph
`remove_edges (justification_graph prob pcf) cut`, from any source `src` that already reaches the
start facts — **provided** none of the path's actions witnesses a cut edge (`Hwit`).

The induction tracks `Hsrc`, the set of currently reachable facts: a delete-relaxed action `a`
with chosen precondition `pcf a` (true, hence already reachable) adds facts `y ∈ a.add`; the
justification edge `pcf a → y` survives the cut by `Hwit`, extending the reachability. -/
private lemma jgraph_reach_of_dr_path {n : ℕ} (prob : STRIPS n)
    (pcf : precondition_choice_function prob) (cut : List (Fin n × Fin n))
    (src : Fin n) :
    ∀ {S T : State n} (p : Path (delete_relaxation prob) S T),
    (∀ (a0 : {b : Action n // b ∈ prob.actions'}),
      delete_relax_action a0.val ∈ p.actionsUsed →
      ∀ y ∈ a0.val.add'.val.toFinset, ((↑(pcf a0) : Fin n), y) ∉ cut) →
    (∀ s ∈ S, Nonempty ((remove_edges (justification_graph prob pcf) cut).Walk src s)) →
    ∀ t ∈ T, Nonempty ((remove_edges (justification_graph prob pcf) cut).Walk src t) := by
  intro S T p
  induction p with
  | empty s => intro _ Hsrc t ht; exact Hsrc t ht
  | cons a s2 ha succ rest ih =>
    rename_i s1 s3
    intro Hwit Hsrc t ht
    obtain ⟨a0, ha0, ha0eq⟩ : ∃ a0, a0 ∈ prob.actions' ∧ delete_relax_action a0 = a := by
      unfold delete_relaxation STRIPS.actions at ha
      simp only [List.coe_toFinset, Set.mem_setOf_eq, List.mem_map] at ha
      exact ha
    have hdel : a.del = (∅ : Set (Fin n)) := dr_action_del_empty prob ha
    have hs2 : s2 = s1 ∪ a.add := by
      have h := succ.2; rw [hdel, Set.diff_empty] at h; exact h
    have Hsrc2 : ∀ x ∈ s2, Nonempty ((remove_edges (justification_graph prob pcf) cut).Walk src x) := by
      intro x hx
      rw [hs2] at hx
      rcases hx with hxS | hxAdd
      · exact Hsrc x hxS
      · set b : {c : Action n // c ∈ prob.actions'} := ⟨a0, ha0⟩ with hb
        have hp0S : (↑(pcf b) : Fin n) ∈ s1 := by
          apply succ.1; rw [← ha0eq]; exact (pcf b).2
        obtain ⟨w⟩ := Hsrc _ hp0S
        have hxAdd' : x ∈ a0.add'.val.toFinset := by rw [← ha0eq] at hxAdd; exact hxAdd
        have hcut : ((↑(pcf b) : Fin n), x) ∉ cut := by
          apply Hwit b _ x hxAdd'
          show delete_relax_action a0 ∈ a :: rest.actionsUsed
          rw [ha0eq]; exact List.mem_cons_self
        have hadj : (remove_edges (justification_graph prob pcf) cut).Adj (↑(pcf b)) x :=
          ⟨⟨b, rfl, hxAdd'⟩, hcut⟩
        exact ⟨w.concat hadj⟩
    have Hwit' : ∀ (a0' : {b : Action n // b ∈ prob.actions'}),
        delete_relax_action a0'.val ∈ rest.actionsUsed →
        ∀ y ∈ a0'.val.add'.val.toFinset, ((↑(pcf a0') : Fin n), y) ∉ cut := by
      intro a0' h y hy
      apply Hwit a0' _ y hy
      show delete_relax_action a0'.val ∈ a :: rest.actionsUsed
      exact List.mem_cons_of_mem _ h
    exact ih Hwit' Hsrc2 t ht

/-- An action witnessing a cut edge `(f, t)` (i.e. `f` is its chosen precondition and `t` one of
its add effects) belongs to the induced landmark. -/
private lemma mem_landmark_induced {n : ℕ} (prob : STRIPS n) (cut : List (Fin n × Fin n))
    (pcf : precondition_choice_function prob)
    (a0 : {b : Action n // b ∈ prob.actions'}) (f t : Fin n)
    (hft : (f, t) ∈ cut) (hf : f = (↑(pcf a0) : Fin n)) (ht : t ∈ a0.val.add'.val.toFinset) :
    a0.val ∈ landmark_induced_by_cut prob cut pcf := by
  unfold landmark_induced_by_cut
  rw [List.mem_flatMap]
  refine ⟨(f, t), hft, ?_⟩
  rw [List.mem_map]
  refine ⟨a0, ?_, rfl⟩
  rw [List.mem_filter]
  exact ⟨List.mem_attach _ _, by simp [hf, ht]⟩

/-- Every action of the induced landmark is an action of the problem. -/
private lemma landmark_subset_actions {n : ℕ} (prob : STRIPS n) (cut : List (Fin n × Fin n))
    (pcf : precondition_choice_function prob) (a : Action n)
    (ha : a ∈ landmark_induced_by_cut prob cut pcf) : a ∈ prob.actions' := by
  unfold landmark_induced_by_cut at ha
  rw [List.mem_flatMap] at ha
  obtain ⟨ft, _, ha⟩ := ha
  rw [List.mem_map] at ha
  obtain ⟨a0, _, rfl⟩ := ha
  exact a0.2

/-- a cut in the justification graph implies a (del-rel) landmark. The idea here is that without the cut, we can never make one of the facts on the "right-hand" side of the cut true and thus also never the goal. This stems from the property that the cut separates the unitary init and goal facts. -/
lemma cuts_in_justification_graph_are_delete_relaxed_landmarks {n : ℕ} (prob : STRIPS n)
    (u_i : unitary_init prob)
    (u_g : unitary_goal prob)
    (pcf : precondition_choice_function prob) (cut : List ((Fin n) × (Fin n))):
    cut_in_graph (justification_graph prob pcf) (get_unitary_init prob u_i) (get_unitary_goal prob u_g) cut → 
      is_delete_relaxed_disjunctive_action_landmark_for_state prob (landmark_induced_by_cut prob cut pcf) prob.init' := by
  intro hcut
  refine ⟨?_, ?_⟩
  · -- Every landmark action is a genuine action, hence its relaxation is in the delete relaxation.
    rw [List.all_eq_true]
    intro a ha
    have ha' : a ∈ prob.actions' := landmark_subset_actions prob cut pcf a ha
    simp only [decide_eq_true_eq]
    show delete_relax_action a ∈ (delete_relaxation prob).actions
    unfold delete_relaxation STRIPS.actions
    simp only [List.coe_toFinset, Set.mem_setOf_eq, List.mem_map]
    exact ⟨a, ha', rfl⟩
  · -- Every delete-relaxed plan uses a landmark action.
    intro plan
    by_contra hcon
    push_neg at hcon
    set i0 := get_unitary_init prob u_i with hi0
    set g0 := get_unitary_goal prob u_g with hg0def
    -- No plan action witnesses a cut edge (else it would be a used landmark action).
    have Hwit : ∀ (a0 : {b : Action n // b ∈ prob.actions'}),
        delete_relax_action a0.val ∈ plan.path.actionsUsed →
        ∀ y ∈ a0.val.add'.val.toFinset, ((↑(pcf a0) : Fin n), y) ∉ cut := by
      intro a0 hused y hy hmemcut
      have hlm : a0.val ∈ landmark_induced_by_cut prob cut pcf :=
        mem_landmark_induced prob cut pcf a0 (↑(pcf a0)) y hmemcut rfl hy
      exact hcon a0.val hlm hused
    -- The unitary initial fact `i0` reaches itself.
    have hinit : convertState prob.init' = ({i0} : Set (Fin n)) := get_unitary_init_is_init prob u_i
    have Hsrc : ∀ s ∈ (convertState prob.init' : State n),
        Nonempty ((remove_edges (justification_graph prob pcf) cut).Walk i0 s) := by
      intro s hs
      rw [hinit, Set.mem_singleton_iff] at hs
      subst hs
      exact ⟨WeightedDiGraph.Walk.nil⟩
    have hreach := jgraph_reach_of_dr_path prob pcf cut i0 plan.path Hwit Hsrc
    -- The unitary goal fact `g0` is true at the end of the plan.
    have hg0 : g0 ∈ plan.last := by
      apply plan.goal
      show g0 ∈ convertVarSet (delete_relaxation prob).goal'
      unfold convertVarSet
      rw [show (delete_relaxation prob).goal' = prob.goal' from rfl, get_unitary_goal_is_goal prob u_g]
      simp [hg0def]
    -- Hence `g0` is reachable from `i0` in the cut graph, contradicting the cut.
    obtain ⟨w⟩ := hreach g0 hg0
    exact hcut.false ⟨w.bypass, WeightedDiGraph.Walk.bypass_isPath w⟩


def zero_cost_reachable [FinEnum V] (g : NatGraph V) (v goal : V) : Bool :=
    let ret := NatGraph.astar (g:=g) (fun _ => 0) v goal
    match ret with
    | .none => false
    | .some p => p.cost = 0


def reachable [FinEnum V] (g : NatGraph V) (v goal : V) : Bool :=
    let ret := NatGraph.astar (g:=g) (fun _ => 0) v goal
    match ret with
    | .none => false
    | .some _ => true


/-- returns all nodes from which the goal can be reached with cost 0 -/
def goal_zone {V : Type} [FinEnum V] (g : NatGraph V) (goal : V) : List V :=
  let vList : List V := (FinEnum.toList (Finset.univ : Finset V))
  vList.filter (fun v => zero_cost_reachable g v goal)

/-- returns all edges that enter the goal zone -/
def edges_entering_goal_zone {V : Type} [FinEnum V] (g : NatGraph V) (goal : V) : List (V × V) :=
  let gz := (goal_zone g goal)

  gz.flatMap (fun v => 
    let vList : List V := (FinEnum.toList (Finset.univ : Finset V))
    vList.filterMap (fun u =>
      if u ∉ gz ∧ decide (g.Adj u v) then .some (u,v)
      else .none
    )
  )


lemma edges_entering_goal_zone_are_edges {V : Type} [FinEnum V] (g : NatGraph V) (goal : V):
    ∀ x ∈ edges_entering_goal_zone g goal, g.Adj x.1 x.2 := by sorry

lemma edges_entering_goal_zone_dont_contain_zero_cost {V : Type} [FinEnum V] (g : NatGraph V) (goal : V):
    ∀ x ∈ edges_entering_goal_zone g goal, g.Payload x.1 x.2 (by sorry) ≠ 0 := by sorry

lemma edges_entering_goal_zone_are_cut_if_init_not_zero_reachable {V : Type} [FinEnum V] (g : NatGraph V) (init : V) (goal : V):
  ¬ zero_cost_reachable g init goal → cut_in_graph g init goal (edges_entering_goal_zone g goal) := by sorry


lemma goal_zone_landmark_of_justification_graph {n : ℕ} (prob : STRIPS n)
    (u_i : unitary_init prob)
    (u_g : unitary_goal prob)
    (pcf : precondition_choice_function prob):
      is_delete_relaxed_disjunctive_action_landmark_for_state prob (landmark_induced_by_cut prob (edges_entering_goal_zone (justification_graph prob pcf) (get_unitary_goal prob u_g)) pcf) prob.init' := by sorry



lemma cost_goal_zone_landmark_of_justification_graph {n : ℕ} (prob : STRIPS n)
    (u_i : unitary_init prob)
    (u_g : unitary_goal prob)
    (pcf : precondition_choice_function prob):
    ¬ zero_cost_reachable (justification_graph prob pcf) (get_unitary_init prob u_i) (get_unitary_goal prob u_g) → 
    ∀ a ∈ (landmark_induced_by_cut prob (edges_entering_goal_zone (justification_graph prob pcf) (get_unitary_goal prob u_g)) pcf), a.cost > 0 := by sorry










/-- runs one step of landmark cutting: compute justification graph, extract cut, generate landmark and partition the cost -/
def lmcut_step {n : ℕ} (prob : STRIPS n)
    --(u_i : unitary_init prob)
    (u_g : unitary_goal prob)
    (pcf : precondition_choice_function prob):
      (List (Action n)) × ℕ × (cost_partitioning prob 2) :=
    let jg := justification_graph prob pcf
    let cut := edges_entering_goal_zone jg (get_unitary_goal prob u_g)
    let lm := landmark_induced_by_cut prob cut pcf
    let minCost := if ne : lm = [] then 0 else
      (lm.map (fun a => a.cost)).min (by simp_all only [ne_eq, map_eq_nil_iff, not_false_eq_true, lm, cut, jg])

    let part : cost_partitioning prob 2 := fun p =>
      match p with
      | 0 => fun a_index => if prob.actions'[a_index] ∈ lm then minCost else 0
      | 1 => fun a_index => if prob.actions'[a_index] ∈ lm then prob.actions'[a_index].cost - minCost else prob.actions'[a_index].cost

    (lm,minCost,part)



def lmcut_step_yields_landmark {n : ℕ} (prob : STRIPS n)
    (u_i : unitary_init prob)
    (u_g : unitary_goal prob)
    (pcf : precondition_choice_function prob):
    is_delete_relaxed_disjunctive_action_landmark_for_state prob (lmcut_step prob u_g pcf).1 prob.init' := by sorry


def lmcut_step_yields_partitioning {n : ℕ} (prob : STRIPS n)
    (u_i : unitary_init prob)
    (u_g : unitary_goal prob)
    (pcf : precondition_choice_function prob):
    is_valid_cost_partitioning prob 2 (lmcut_step prob u_g pcf).2.2 := by sorry


def lmcut_step_yields_landmark_with_heuristic_in_partition {n : ℕ} (prob : STRIPS n)
    (u_i : unitary_init prob)
    (u_g : unitary_goal prob)
    (pcf : precondition_choice_function prob)
    (i_g_reachable : reachable (justification_graph prob pcf) (get_unitary_init prob u_i) (get_unitary_goal prob u_g)) :
    (lmcut_step prob u_g pcf).2.1 = 
      elementary_landmark_heuristic (partition_STRIPS prob (lmcut_step prob u_g pcf).2.2 ⟨0, by sorry⟩) (lmcut_step prob u_g pcf).1 prob.init'
    := by sorry

def lmcut_step_yields_non_zero_heuristic {n : ℕ} (prob : STRIPS n)
    (u_i : unitary_init prob)
    (u_g : unitary_goal prob)
    (pcf : precondition_choice_function prob)
    (i_g_reachable : reachable (justification_graph prob pcf) (get_unitary_init prob u_i) (get_unitary_goal prob u_g)) 
    (i_g_not_zero_reachable : ¬ zero_cost_reachable (justification_graph prob pcf) (get_unitary_init prob u_i) (get_unitary_goal prob u_g)) :
    (lmcut_step prob u_g pcf).2.1 > 0 := by sorry


def lmcut_inner {n : ℕ} (prob : STRIPS n)
    (u_i : unitary_init prob)
    (u_g : unitary_goal prob)
    (pcf : Π p : STRIPS n, precondition_choice_function p):
      List (List (Action n)) × ℕ × Σ p : ℕ, (cost_partitioning prob p) :=
    
    let jg := justification_graph prob (pcf prob)
    let i := (get_unitary_init prob u_i)
    let goal := (get_unitary_goal prob u_g)

    -- return no partitioning
    if ¬ reachable jg i goal then ([[]], (2 ^ n) * max_action_cost prob , by sorry)
    -- return no partitioning
    else if zero_cost_reachable jg i goal then ([], 0, by sorry)
    else
     let r := lmcut_step prob u_g (pcf prob)
     let subprob := partition_STRIPS prob r.2.2 ⟨1, by sorry⟩

     let subret := lmcut_inner subprob u_i u_g pcf

     let lms : List (List (Action n)):= r.1 :: subret.1
     let hval : ℕ := r.2.1 + subret.2.1
     let parts : Σ p : ℕ, (cost_partitioning prob p) := by sorry -- take r.2.2 0 and replace r.2.2 1 with the subpartitioning found by subret.2.2
     (lms, hval, parts)

termination_by (prob.actions'.map (fun a => a.cost)).sum -- decreases due to non-zero partitioning
decreasing_by
  sorry


/-- lmcut essentially returns a cost partioning over elementary landmark heuritics. Costpartitioning preserves admissibility and elementary landmark heuristics are admissible, so admissibility for init follows. Note that the lm_cut inner version does not yet take the actual state into account, it computes an estimate only for init -/
lemma lmcut_inner_admissible_for_init {n : ℕ} (prob : STRIPS n)
    (u_i : unitary_init prob)
    (u_g : unitary_goal prob)
    (pcf : Π p : STRIPS n, precondition_choice_function p):
      ∀ plan : Plan prob prob.init, plan.path.cost ≥ (lmcut_inner prob u_i u_g pcf).2.1 := by sorry
