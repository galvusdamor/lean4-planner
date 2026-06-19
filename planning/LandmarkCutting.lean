import planning.Landmark
import planning.CostPartitioning
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Set.Card

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
  induction p <;> simp_all [ Path.append ]
  · rfl
  · simp_all [ Path.cost ]
    ring

/--
In a delete relaxation every action has an empty delete effect.
-/
private lemma dr_action_del_empty {n : ℕ} (X : STRIPS n) {a : Action n}
    (ha : a ∈ (delete_relaxation X).actions) : a.del = ∅ := by
  unfold delete_relaxation at ha; simp_all [ STRIPS.actions ]
  obtain ⟨ b, hb, rfl ⟩ := ha; unfold delete_relax_action; simp [ Action.del ]
  unfold convertVarSet; simp

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
  induction' p with a s2 s3 ha succ p ih generalizing T0
  · exact ⟨ T0, hi, hsub, Path.empty T0, rfl ⟩
  · obtain ⟨a, ha_mem, ha_eq⟩ : ∃ a ∈ prob.actions', s2 = delete_relax_action a := by
      unfold delete_relaxation at p; simp_all [ STRIPS.actions ]
      grind
    -- Define the embedded action `e` in the normal form.
    set e : Action (n + 2) := delete_relax_action (Action.mk a.name ⟨a.pre'.val.map (Fin.castLE (by omega)) ++ [⟨n, by omega⟩], sortedLT_append_top (sortedLT_map_castLE (by omega) a.pre'.property) (by
      intro x hx
      simp only [mem_map] at hx
      obtain ⟨y, _, rfl⟩ := hx
      simpa only [Fin.lt_def, Fin.val_castLE] using y.isLt)⟩ ⟨a.add'.val.map (Fin.castLE (by omega)), sortedLT_map_castLE (by omega) a.add'.property⟩ ⟨a.del'.val.map (Fin.castLE (by omega)), sortedLT_map_castLE (by omega) a.del'.property⟩ a.cost)
    -- Show that `e` is in the actions of the delete-relaxed normal form.
    have he_mem : e ∈ (delete_relaxation (i_g_normal_form prob)).actions := by
      unfold delete_relaxation i_g_normal_form; simp [ STRIPS.actions, List.mem_map ]
      exact Or.inr <| Or.inr <| ⟨ a, ha_mem, rfl ⟩
    have he_pre : e.pre ⊆ T0 := by
      intro x hx
      unfold e at hx; simp_all [ delete_relax_action, Action.pre ]
      unfold convertVarSet at hx; simp_all
      rcases hx with ( rfl | ⟨ y, hy, rfl ⟩ ) <;> [ exact hi; exact hsub y ( by
        exact ih.1 ( by unfold Action.pre; unfold convertVarSet; simp; subst ha_eq; simp_all only [e] ) ) ]
    have he_succ : Successor e T0 (T0 ∪ e.add) := by
      refine ⟨he_pre, ?_⟩
      rw [show e.del = ∅ from dr_action_del_empty _ he_mem, Set.diff_empty]
    rename_i h
    obtain ⟨ T2, hT2₁, hT2₂, q, hq ⟩ := h ( show ⟨ n, by omega ⟩ ∈ T0 ∪ e.add from by
                                              grind ) ( show ∀ x ∈ ha, Fin.castLE ( by omega ) x ∈ T0 ∪ e.add from by
                                                                                                  intro x hx; specialize ih; cases ih; simp_all [ Successor ]
                                                                                                  unfold e; simp [ delete_relax_action ]
                                                                                                  unfold delete_relax_action at hx; simp_all [ Action.del, Action.add ]
                                                                                                  unfold convertVarSet at *; simp_all
                                                                                                  grind )
    use T2, hT2₁, hT2₂, Path.cons e (T0 ∪ e.add) (by
    exact he_mem) (by
    exact he_succ) q
    simp [ *, Path.cost ]
    unfold e; simp [ delete_relax_action ]

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
  revert plan
  intro plan
  obtain ⟨last, p, hgoal⟩ := plan
  have h_init : (delete_relaxation (i_g_normal_form prob)).init = {y | y = (⟨n, by omega⟩ : Fin (n + 2))} := by
    unfold delete_relaxation i_g_normal_form; simp [ STRIPS.init ]
    ext ⟨x, hx⟩; simp [convertState, BitVec.getElem_twoPow]
  obtain ⟨T0, hT0⟩ : ∃ T0 : State (n + 2), (⟨n, by omega⟩ : Fin (n + 2)) ∈ T0 ∧ (∀ x ∈ (delete_relaxation prob).init, (Fin.castLE (show n ≤ n + 2 by omega) x) ∈ T0) ∧ ∃ q : Path (delete_relaxation (i_g_normal_form prob)) (delete_relaxation (i_g_normal_form prob)).init T0, q.cost = 0 := by
                                                                                                                                    use {y | y = (⟨n, by omega⟩ : Fin (n + 2))} ∪ (delete_relaxation prob).init.image (Fin.castLE (show n ≤ n + 2 by omega))
                                                                                                                                    refine' ⟨ _, _, _ ⟩
                                                                                                                                    · exact Set.mem_union_left _ rfl
                                                                                                                                    · exact fun x hx => Or.inr ⟨ x, hx, rfl ⟩
                                                                                                                                    · constructor
                                                                                                                                      swap
                                                                                                                                      refine' Path.cons _ _ _ _ ( Path.empty _ )
                                                                                                                                      exact delete_relax_action ( Action.mk "init" ⟨ [ ⟨ n, by omega ⟩ ], by grind ⟩ ⟨ ( varset'_of_state' prob.init' ).val.map ( Fin.castLE ( by omega ) ), sortedLT_map_castLE ( by omega ) ( varset'_of_state' prob.init' ).property ⟩ ⟨ [ ], by apply List.sortedLT_iff_pairwise.mpr ; simp ⟩ 0 )
                                                                                                                                      all_goals norm_num [ delete_relax_action, Successor ]
                                                                                                                                      all_goals norm_num [ Applicable, Successor, Path.cost ]
                                                                                                                                      · unfold delete_relaxation i_g_normal_form; simp [ STRIPS.actions, List.mem_map ]
                                                                                                                                        exact Or.inl rfl
                                                                                                                                      · simp [ Set.subset_def, Set.ext_iff ]
                                                                                                                                        simp [ h_init, Action.pre, Action.add, Action.del ]
                                                                                                                                        simp [ convertVarSet, varset'_of_state' ]
                                                                                                                                        simp [ delete_relaxation, STRIPS.init, convertState ]
  obtain ⟨T2, hT2₁, hT2₂, q, hq⟩ := lift_forward prob p hT0.left hT0.right.left
  -- Construct the goal step
  obtain ⟨aG, haG⟩ : ∃ aG : Action (n + 2), aG ∈ (delete_relaxation (i_g_normal_form prob)).actions ∧ aG.pre ⊆ T2 ∧ aG.del = ∅ ∧ aG.cost = 0 ∧ aG.add = {⟨n + 1, by omega⟩} := by
    unfold delete_relaxation i_g_normal_form; simp [ STRIPS.actions, List.mem_map ]
    refine Or.inr <| Or.inl ⟨ ?_, ?_, ?_, ?_ ⟩ <;> simp [ delete_relax_action ]
    · intro x hx; unfold Action.pre at hx; unfold convertVarSet at hx; simp_all
      obtain ⟨ a, ha, rfl ⟩ := hx; exact hT2₂ a ( hgoal ( by unfold convertVarSet; simp; obtain ⟨left, right⟩ := hT0; obtain ⟨left_1, right⟩ := right; obtain ⟨w, h⟩ := right; exact ha ) )
    · unfold Action.del; simp [ convertVarSet ]
    · unfold Action.add; simp [ convertVarSet ]
  obtain ⟨q', hq'⟩ : ∃ q' : Path (delete_relaxation (i_g_normal_form prob)) T2 (T2 ∪ aG.add), q'.cost = 0 := by
    use Path.cons aG (T2 ∪ aG.add) haG.left (by
    unfold Successor
    simp_all only [Set.setOf_eq_eq_singleton, Set.union_singleton, Set.diff_empty, and_self]) (Path.empty (T2 ∪ aG.add))
    simp [ Path.cost, haG ]
  use ⟨T2 ∪ aG.add, (hT0.right.right.choose.append q).append q', by
    unfold delete_relaxation i_g_normal_form at *; simp_all [ STRIPS.GoalState, convertVarSet ] ;⟩
  simp only [Path.cost_append, hT0.right.right.choose_spec, hq, hq', Nat.zero_add, Nat.add_zero]

/--
Delete-relaxed paths are monotone: facts are only ever added.
-/
private lemma dr_path_mono {n : ℕ} {pt : STRIPS n} (hdel : ∀ a ∈ pt.actions, a.del = ∅)
    {s1 s2 : State n} (p : Path pt s1 s2) : s1 ⊆ s2 := by
  induction p
  · exact Set.Subset.refl _
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
  induction q
  · tauto
  · rename_i a s1 s2 s3 ha succ π ih
    by_cases h : ⟨n + 1, by omega⟩ ∈ s2 <;> simp_all [ Successor ]
    unfold delete_relaxation i_g_normal_form at ha; simp_all [ STRIPS.actions, List.mem_map ]
    rcases ha with ( rfl | rfl | ⟨ a, ha, rfl ⟩ ) <;> simp_all [ delete_relax_action, Action.add ]
    · unfold convertVarSet at h; simp_all
      obtain ⟨ a, ha, ha' ⟩ := h; replace ha' := congr_arg Fin.val ha'; simp_all
      grind
    · have := dr_path_mono ( show ∀ a ∈ ( delete_relaxation ( i_g_normal_form prob ) ).actions, a.del = ∅ from fun a ha => dr_action_del_empty _ ha ) π; simp_all [ Set.subset_def ]
      simp_all [ Action.pre, Action.del ]
      unfold convertVarSet at *; simp_all
    · unfold convertVarSet at h; simp_all
      obtain ⟨ x, hx, hx' ⟩ := h; have := Fin.is_lt x; simp_all [ Fin.ext_iff ]

/--
Projecting `Fin.castLE`-embedded membership back: `emb x` lies in the image list iff `x` lies in
the original list (`Fin.castLE` is injective).
-/
private lemma castLE_mem_map_castLE {n m : ℕ} (h : n ≤ m) (l : List (Fin n)) (x : Fin n) :
    (Fin.castLE h x) ∈ (l.map (Fin.castLE h)).toFinset ↔ x ∈ l.toFinset := by
  simp_all only [mem_toFinset, mem_map, Fin.castLE_inj, exists_eq_right]

/--
Prepending a projected original action to an original delete-relaxed path.
-/
private lemma project_cons_embedded {n : ℕ} (prob : STRIPS n) {a : Action n}
    (ha : a ∈ prob.actions') {D0 F : State n} (hpre : a.pre ⊆ D0)
    (dq : Path (delete_relaxation prob) (D0 ∪ a.add) F) :
    ∃ dq' : Path (delete_relaxation prob) D0 F, dq'.cost = dq.cost + a.cost := by
  use Path.cons (delete_relax_action a) (D0 ∪ a.add) (by
  unfold delete_relaxation; simp [ STRIPS.actions, List.mem_map ]
  grind) (by
  unfold Successor; simp_all [ delete_relax_action, Action.pre, Action.add, Action.del ]
  unfold convertVarSet at *; simp_all
  exact fun x hx => hpre <| by unfold Action.pre at hx; unfold convertVarSet at hx; simp_all ;) dq
  simp [ Path.cost, delete_relax_action ]

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
          exact absurd this (Nat.ne_of_lt (hlt.trans (Nat.lt_succ_self n)))
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
    exact absurd hval (Nat.ne_of_lt x.isLt)
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
       contrapose! hsolv
       simp_all only
     -- Let `rdp := (planner dp (fun _ => 0)).get hdp` and `rep := (planner ep (fun _ => 0)).get hep`.
     obtain ⟨rdp, hrdp⟩ : ∃ rdp, (Validator.planner (Validator.delete_relaxation prob) (fun _ => 0)) = some rdp := by
       exact Option.isSome_iff_exists.mp ( by exact Option.isSome_iff_ne_none.mpr fun h => hsolv <| Validator.planner_complete _ _ h )
     obtain ⟨rep, hrep⟩ : ∃ rep, (Validator.planner (Validator.delete_relaxation (i_g_normal_form prob)) (fun _ => 0)) = some rep := by
       obtain ⟨eplan, heplan⟩ : ∃ eplan : Plan (delete_relaxation (i_g_normal_form prob)) (delete_relaxation (i_g_normal_form prob)).init, True := by
         exact ⟨ ignf_dr_plan_of_dr_plan prob dplan |> Classical.choose, trivial ⟩
       have := planner_complete ( delete_relaxation ( i_g_normal_form prob ) ) ( fun _ => 0 ) ; simp_all [ Unsolvable ]
       cases h : planner ( delete_relaxation ( i_g_normal_form prob ) ) ( fun x => 0 ) <;> simp_all [ UnsolvableState ]
       exact this.elim eplan
     obtain ⟨eplan, heplan⟩ : ∃ eplan, (Validator.planner (Validator.delete_relaxation (i_g_normal_form prob)) (fun _ => 0)) = some eplan ∧ eplan.path.cost ≤ rdp.path.cost := by
       obtain ⟨eplan, heplan⟩ : ∃ eplan, (Validator.planner (Validator.delete_relaxation (i_g_normal_form prob)) (fun _ => 0)) = some eplan ∧ eplan.path.cost ≤ rdp.path.cost := by
         have := ignf_dr_plan_of_dr_plan prob rdp
         obtain ⟨eplan, heplan⟩ := this
         have := Validator.planner_optimal (Validator.delete_relaxation (Validator.i_g_normal_form prob)) (fun _ => 0) (Validator.zero_heur_admissible (Validator.delete_relaxation (Validator.i_g_normal_form prob))) (by
         exact hrep.symm ▸ rfl) eplan
         grind
       use eplan
     obtain ⟨plan, hplan⟩ : ∃ plan, (Validator.planner (Validator.delete_relaxation prob) (fun _ => 0)) = some plan ∧ plan.path.cost ≤ rep.path.cost := by
       obtain ⟨plan, hplan⟩ : ∃ plan : Plan (Validator.delete_relaxation prob) (Validator.delete_relaxation prob).init, plan.path.cost ≤ rep.path.cost := by
         exact ⟨ _, dr_plan_of_ignf_dr_plan prob rep |> Classical.choose_spec ⟩
       have := Validator.planner_optimal ( Validator.delete_relaxation prob ) ( fun _ => 0 ) ( Validator.zero_heur_admissible ( Validator.delete_relaxation prob ) ) ( show ( Validator.planner ( Validator.delete_relaxation prob ) ( fun _ => 0 ) ).isSome from by
                                                                                                                                                                         grind ) plan
       grind
     unfold h_plus
     simp_all [ delete_relaxation ]
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

/-- A planning problem `prob` *has preconditions* if every one of its actions has at least one
precondition fact.  This is exactly the condition under which a `precondition_choice_function prob`
can exist (the subtype `{ p : Fin n // p ∈ a.val.pre }` is nonempty for every action).  The i/g
normal form of a problem with a nonempty goal always has this property, and cost partitioning
preserves it. -/
def has_preconditions {n : ℕ} (prob : STRIPS n) : Prop :=
  ∀ a ∈ prob.actions', a.pre'.val ≠ []

/-- An element of `a.val.pre'.val` is a member of `a.val.pre` (the `Set`-level precondition). -/
lemma mem_pre_of_mem_pre'_val {n : ℕ} (a : Action n) {x : Fin n} (hx : x ∈ a.pre'.val) :
    x ∈ a.pre := by
  unfold Action.pre convertVarSet
  simpa using hx

/-
Cost partitioning preserves `has_preconditions`: it only relabels action costs, leaving the
preconditions untouched.
-/
lemma partition_STRIPS_has_preconditions {n P : ℕ} (prob : STRIPS n)
    (partitioning : cost_partitioning prob P) (p : Fin P)
    (hp : has_preconditions prob) :
    has_preconditions (partition_STRIPS prob partitioning p) := by
  unfold has_preconditions at *
  simp_all [ partition_STRIPS ]
  grind

/-
The i/g normal form of a problem with a nonempty goal has preconditions: every embedded action
gains the auxiliary `i` variable as a precondition, the `init` action has `{i}` as precondition,
and the `goal` action has the (nonempty) embedded goal as precondition.
-/
lemma i_g_normal_form_has_preconditions {n : ℕ} (prob : STRIPS n)
    (hg : prob.goal'.val ≠ []) :
    has_preconditions (i_g_normal_form prob) := by
  unfold has_preconditions; simp_all [ i_g_normal_form ]
  rintro a ( ⟨ b, hb, rfl ⟩ | rfl | rfl ) <;> simp [ hg ]

/-- A precondition choice function is *relax invariant* if it picks the same precondition for any
two actions that have the same delete relaxation (i.e. that agree on name, preconditions, add- and
delete-effects modulo the delete effect, and on cost).  Such pcfs make the induced landmark closed
under delete-relaxation equivalence, which is exactly what is needed to turn a delete-relaxed
landmark into a genuine one.  A canonical pcf (e.g. "pick the smallest precondition") is relax
invariant.

NOTE: this invariant is **no longer needed** for the admissibility of `lmcut` (see
`lmcut_admissible`, `lmcut_inner_admissible_for_init`).  Admissibility holds for *every* pcf, because
each step charges its value on the whole relax-equivalence class of the cut-induced landmark
(`get_all_equiv_delete_relaxed_actions`), which is a genuine landmark unconditionally.  The
definition and `landmark_induced_closed_under_relax` below are kept only for documentation. -/
def relax_invariant_pcf {n : ℕ} (prob : STRIPS n) (pcf : precondition_choice_function prob) : Prop :=
  ∀ (a b : {x : Action n // x ∈ prob.actions'}),
    delete_relax_action a.val = delete_relax_action b.val → (↑(pcf a) : Fin n) = (↑(pcf b) : Fin n)



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

/-
The initial state, viewed as a `Set (Fin n)`, is the coercion of the finite set of variables
that are `true` in the underlying bit vector `prob.init'`.
-/
lemma init_eq_varset_toFinset {n : ℕ} (prob : STRIPS n) :
    prob.init = ↑(varset'_of_state' prob.init').val.toFinset := by
      convert Set.ext _
      intro x; unfold STRIPS.init; simp [ convertState, varset'_of_state'_mem ]

/-
The number of true variables in the initial state equals the length of the sorted list of
true variables of `prob.init'`.
-/
lemma init_ncard_eq_varset_length {n : ℕ} (prob : STRIPS n) :
    prob.init.ncard = (varset'_of_state' prob.init').val.length := by
      rw [init_eq_varset_toFinset, Set.ncard_coe_finset, List.toFinset_card_of_nodup]
      exact List.Pairwise.imp_of_mem ( fun x y hxy => by simpa using ne_of_lt hxy ) ( List.sortedLT_iff_pairwise.mp ( varset'_of_state' prob.init' |>.property ) )

/-- For a unitary initial state the sorted list of true variables has length exactly one. -/
lemma unitary_init_varset_length {n : ℕ} (prob : STRIPS n) (u : unitary_init prob) :
    (varset'_of_state' prob.init').val.length = 1 := by
  rw [← init_ncard_eq_varset_length]
  have := u; simp only [unitary_init, beq_iff_eq] at this; exact this

/-- Computable extraction of the single initial fact, read directly off the bit vector
`prob.init'` (its unique true variable). -/
def get_unitary_init {n : ℕ} (prob : STRIPS n) (u : unitary_init prob) : Fin n :=
  (varset'_of_state' prob.init').val.head (by
    have h := unitary_init_varset_length prob u
    intro hnil; rw [hnil, List.length_nil] at h; exact absurd h (by omega))

def get_unitary_goal{n : ℕ} (prob : STRIPS n) (u : unitary_goal prob) : Fin n :=
  prob.goal'.val.head (by unfold unitary_goal at u ; grind)

lemma get_unitary_init_is_init {n : ℕ} (prob : STRIPS n) (u : unitary_init prob):
    prob.init = {get_unitary_init prob u} := by
  have h := unitary_init_varset_length prob u
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp h
  have hhead : get_unitary_init prob u = a := by simp [get_unitary_init, ha]
  rw [init_eq_varset_toFinset, hhead, ha]
  simp

lemma get_unitary_goal_is_goal {n : ℕ} (prob : STRIPS n) (u : unitary_goal prob):
    prob.goal'.val = [get_unitary_goal prob u] := by
  have hlen : prob.goal'.val.length = 1 := by
    have := u; simp only [unitary_goal, beq_iff_eq] at this; exact this
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hlen
  simp [get_unitary_goal, ha]



/-- the justification graph selects one precondition per action and connects facts using them - and ignoring their deleting effects. We use NatGraph here, as we have search algorithms for them -/
def justification_graph {n : ℕ} (prob : STRIPS n) (pcf : precondition_choice_function prob) : NatGraph (Fin n) :=
  -- We quantify over the subtype `{b // b ∈ prob.actions'}` so that the precondition choice
  -- function `pcf` can be applied directly (it needs the membership witness).  Membership is
  -- phrased through `a.val.add'.val.toFinset`, which is definitionally `t ∈ a.val.add`, so that
  -- the relation is decidable.
  let edges : Fin n → Fin n → Prop := fun f t =>
    ∃ a : {b : Action n // b ∈ prob.actions'}, f = (↑(pcf a) : Fin n) ∧ t ∈ a.val.add'.val.toFinset

  let dg : Digraph (Fin n) := Digraph.mk edges
  let dg_dec : DecidableRel dg.Adj := fun f t => inferInstanceAs (Decidable (edges f t))

  -- cost of an edge is the cheapest cost of an action that created that edge.  We filter the
  -- *attached* action list so that `pcf a` (which needs the membership witness) and `a.val.add'`
  -- are well typed, and we collect the underlying actions afterwards.
  let cost : (u v : Fin n) → dg.Adj u v → ℕ := fun f t adj =>
    let edgeActions : List (Action n) := (prob.actions'.attach.filter (fun a =>
      decide (f = (↑(pcf a) : Fin n) ∧ t ∈ a.val.add'.val.toFinset))).map (·.val)
    (edgeActions.map (·.cost)).min (by
      obtain ⟨a, hf, ht⟩ := adj
      have ha : a.val ∈ edgeActions := by
        simp only [edgeActions, List.mem_map, List.mem_filter]
        exact ⟨a, ⟨List.mem_attach _ _, by simp [hf, ht]⟩, rfl⟩
      simp only [ne_eq, List.map_eq_nil_iff]
      exact List.ne_nil_of_mem ha)

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

/-
For a relax-invariant pcf, the induced landmark is closed under delete-relaxation equivalence:
if `a` is in the landmark and `b` is an action of the problem with the same delete relaxation,
then `b` is in the landmark as well.

This lemma is no longer used by the admissibility proof (which charges the entire relax-equivalence
class via `get_all_equiv_delete_relaxed_actions` instead); it is retained for documentation.
-/
lemma landmark_induced_closed_under_relax {n : ℕ} (prob : STRIPS n) (cut : List (Fin n × Fin n))
    (pcf : precondition_choice_function prob) (hinv : relax_invariant_pcf prob pcf)
    {a b : Action n} (ha : a ∈ landmark_induced_by_cut prob cut pcf)
    (hb : b ∈ prob.actions') (hrel : delete_relax_action b = delete_relax_action a) :
    b ∈ landmark_induced_by_cut prob cut pcf := by
  -- By definition of `landmark_induced_by_cut`, we know that `a` is in the landmark.
  unfold landmark_induced_by_cut at ha
  simp +zetaDelta at *
  obtain ⟨ c, ⟨ ha₁, ha₂ ⟩, ha₃ ⟩ := ha
  convert mem_landmark_induced prob cut pcf ⟨ b, hb ⟩ ( pcf ⟨ a, ha₁ ⟩ ) c ha₂ _ _ using 1
  · exact hinv ⟨ b, hb ⟩ ⟨ a, ha₁ ⟩ hrel ▸ rfl
  · unfold delete_relax_action at hrel
    simp_all only [Action.mk.injEq, true_and, mem_toFinset]

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
      haveI := g.instDecAdj u v
      if u ∉ gz ∧ g.Adj u v then .some (u,v)
      else .none
    )
  )


/-- The constant-zero heuristic is admissible (costs are natural numbers, so `0` underestimates). -/
lemma zero_heur_graph_admissible {V : Type} [FinEnum V] (g : NatGraph V) (goal : V) :
    g.admissible (fun _ => 0) goal := by
  intro v p; exact Nat.zero_le _

/-
A zero-cost walk witnesses `zero_cost_reachable`.
-/
lemma zero_cost_reachable_of_walk {V : Type} [FinEnum V] (g : NatGraph V) {v goal : V}
    (w : g.Walk v goal) (hw : w.cost = 0) : zero_cost_reachable g v goal := by
      have h_path : ∃ p : g.Path v goal, p.cost = 0 := by
        exact ⟨ ⟨ w.bypass, WeightedDiGraph.Walk.bypass_isPath w ⟩, by simpa using Nat.le_antisymm ( Nat.le_trans ( by exact ( WeightedDiGraph.Walk.cost_bypass_le w ) ) hw.le ) ( Nat.zero_le _ ) ⟩
      obtain ⟨p, hp⟩ : ∃ p : g.Path v goal, p.cost = 0 := h_path
      have h_complete : (NatGraph.astar (g:=g) (fun _ => 0) v goal).isSome := by
        apply NatGraph.astar_is_complete
        exact ⟨ p, rfl ⟩
      have h_optimal : ((NatGraph.astar (g:=g) (fun _ => 0) v goal).get h_complete).cost ≤ p.cost := by
        apply NatGraph.astar_is_optimal
        exact zero_heur_graph_admissible g goal
      have h_zero : ((NatGraph.astar (g:=g) (fun _ => 0) v goal).get h_complete).cost = 0 := by
        exact le_antisymm ( h_optimal.trans hp.le ) ( Nat.zero_le _ )
      simp [zero_cost_reachable] at *
      rw [ show NatGraph.astar ( fun x => 0 ) v goal = some ( ( NatGraph.astar ( fun x => 0 ) v goal ).get h_complete ) from Option.eq_some_of_isSome h_complete ] ; simp [ h_zero ]

/-
`zero_cost_reachable` yields a zero-cost walk.
-/
lemma walk_of_zero_cost_reachable {V : Type} [FinEnum V] (g : NatGraph V) {v goal : V}
    (h : zero_cost_reachable g v goal) : ∃ w : g.Walk v goal, w.cost = 0 := by
      contrapose! h
      unfold zero_cost_reachable
      cases h' : NatGraph.astar ( fun _ => 0 ) v goal <;> simp_all

/-- Membership in the goal zone is exactly zero-cost reachability. -/
lemma mem_goal_zone_iff {V : Type} [FinEnum V] (g : NatGraph V) (goal v : V) :
    v ∈ goal_zone g goal ↔ zero_cost_reachable g v goal := by
  unfold goal_zone
  rw [List.mem_filter]
  simp [FinEnum.mem_toList]

/-- The goal lies in its own goal zone (the empty walk has cost `0`). -/
lemma goal_mem_goal_zone {V : Type} [FinEnum V] (g : NatGraph V) (goal : V) :
    goal ∈ goal_zone g goal := by
  rw [mem_goal_zone_iff]
  exact zero_cost_reachable_of_walk g WeightedDiGraph.Walk.nil (by simp [WeightedDiGraph.Walk.cost])

/-
Converse of `edges_entering_goal_zone_are_edges`: every edge crossing from outside the goal
zone into it is recorded by `edges_entering_goal_zone`.
-/
lemma mem_edges_entering_goal_zone {V : Type} [FinEnum V] (g : NatGraph V) (goal : V) {u v : V}
    (hu : u ∉ goal_zone g goal) (hv : v ∈ goal_zone g goal) (hadj : g.Adj u v) :
    (u, v) ∈ edges_entering_goal_zone g goal := by
      unfold edges_entering_goal_zone; simp [ List.mem_flatMap, List.mem_filterMap, hv, hu, hadj ]

/-
In the cut graph (all edges entering the goal zone removed), any walk that ends inside the
goal zone must also start inside it.
-/
lemma walk_start_in_goal_zone {V : Type} [FinEnum V] (g : NatGraph V) (goal : V) {u v : V}
    (w : (remove_edges g (edges_entering_goal_zone g goal)).Walk u v)
    (hv : v ∈ goal_zone g goal) : u ∈ goal_zone g goal := by
      revert w
      intro w
      induction' w with u w ih
      · exact hv
      · rename_i h₁ h₂ h₃
        contrapose! h₁; simp_all [ remove_edges ]
        exact fun h => mem_edges_entering_goal_zone g goal h₁ h₃ h

lemma edges_entering_goal_zone_are_edges {V : Type} [FinEnum V] (g : NatGraph V) (goal : V):
    ∀ x ∈ edges_entering_goal_zone g goal, g.Adj x.1 x.2 := by
      unfold edges_entering_goal_zone; simp [ List.mem_flatMap ]
      grind

lemma edges_entering_goal_zone_dont_contain_zero_cost {V : Type} [FinEnum V] (g : NatGraph V) (goal : V):
    ∀ x, (h : x ∈ edges_entering_goal_zone g goal) →
      g.Payload x.1 x.2 (edges_entering_goal_zone_are_edges g goal x h) ≠ 0 := by
        intro x hx
        obtain ⟨_, _, _, _, h_adj⟩ : ∃ u v, x = (u, v) ∧ u ∉ goal_zone g goal ∧ v ∈ goal_zone g goal ∧ g.Adj u v := by
          unfold edges_entering_goal_zone at hx; simp_all [ List.mem_flatMap, List.mem_filterMap ]
          grind
        rename_i u v hu hv
        contrapose! hv
        obtain ⟨w2, hw2⟩ : ∃ w2 : g.Walk v goal, w2.cost = 0 := by
          exact walk_of_zero_cost_reachable g ( by rw [ mem_goal_zone_iff ] at h_adj; exact h_adj.1 )
        obtain ⟨w1, hw1⟩ : ∃ w1 : g.Walk u v, w1.cost = 0 := by
          use WeightedDiGraph.Walk.cons h_adj.2 WeightedDiGraph.Walk.nil
          subst hu
          simp_all only
          obtain ⟨left, right⟩ := h_adj
          exact hv
        exact mem_goal_zone_iff g goal u |>.2 ( zero_cost_reachable_of_walk g ( w1.append w2 ) ( by simp [ hw1, hw2, WeightedDiGraph.Walk.append_cost ] ) )

lemma edges_entering_goal_zone_are_cut_if_init_not_zero_reachable {V : Type} [FinEnum V] (g : NatGraph V) (init : V) (goal : V):
  ¬ zero_cost_reachable g init goal → cut_in_graph g init goal (edges_entering_goal_zone g goal) := by
  intro hinit
  refine ⟨fun p => ?_⟩
  have hstart := walk_start_in_goal_zone g goal p.val (goal_mem_goal_zone g goal)
  exact hinit ((mem_goal_zone_iff g goal init).mp hstart)


/- The original statement of `goal_zone_landmark_of_justification_graph` (preserved below in a
comment) lacked any reachability hypothesis:

lemma goal_zone_landmark_of_justification_graph {n : ℕ} (prob : STRIPS n)
    (u_i : unitary_init prob) (u_g : unitary_goal prob)
    (pcf : precondition_choice_function prob):
      is_delete_relaxed_disjunctive_action_landmark_for_state prob (landmark_induced_by_cut prob (edges_entering_goal_zone (justification_graph prob pcf) (get_unitary_goal prob u_g)) pcf) prob.init'

With the new (minimum-action) edge costs this is **false**: if the unitary init fact is
zero-cost reachable to the unitary goal in the justification graph, then `init` lies in the goal
zone, no edge enters the goal zone from `init`'s side, the induced landmark can be empty, yet a
(zero cost) delete-relaxed plan exists — so the landmark property fails.  The faithful statement
adds the hypothesis `¬ zero_cost_reachable …`, exactly the situation in which the edges entering
the goal zone form a genuine init/goal cut. -/
lemma goal_zone_landmark_of_justification_graph {n : ℕ} (prob : STRIPS n)
    (u_i : unitary_init prob)
    (u_g : unitary_goal prob)
    (pcf : precondition_choice_function prob)
    (i_g_not_zero_reachable : ¬ zero_cost_reachable (justification_graph prob pcf)
      (get_unitary_init prob u_i) (get_unitary_goal prob u_g)):
      is_delete_relaxed_disjunctive_action_landmark_for_state prob (landmark_induced_by_cut prob (edges_entering_goal_zone (justification_graph prob pcf) (get_unitary_goal prob u_g)) pcf) prob.init' :=
  cuts_in_justification_graph_are_delete_relaxed_landmarks prob u_i u_g pcf _
    (edges_entering_goal_zone_are_cut_if_init_not_zero_reachable _ _ _ i_g_not_zero_reachable)



/-- `reachable` yields an actual walk. -/
lemma walk_of_reachable {V : Type} [FinEnum V] (g : NatGraph V) {v goal : V}
    (h : reachable g v goal) : Nonempty (g.Walk v goal) := by
  unfold reachable at h
  cases h' : NatGraph.astar (g:=g) (fun _ => 0) v goal with
  | none => rw [h'] at h; simp at h
  | some p => exact ⟨p.val⟩

/-- If a walk leads from outside the goal zone into it, then at least one edge enters the goal
zone, so `edges_entering_goal_zone` is nonempty. -/
lemma edges_entering_goal_zone_nonempty {V : Type} [FinEnum V] (g : NatGraph V) (goal : V) {u v : V}
    (w : g.Walk u v) (hv : v ∈ goal_zone g goal) (hu : u ∉ goal_zone g goal) :
    edges_entering_goal_zone g goal ≠ [] := by
  induction w with
  | nil => exact absurd hv hu
  | @cons f w0 t adj rest ih =>
    by_cases hw0 : w0 ∈ goal_zone g goal
    · exact List.ne_nil_of_mem (mem_edges_entering_goal_zone g goal hu hw0 adj)
    · exact ih hv hw0

/-
**An optimal path does not benefit from leaving the goal zone.**

Any walk `W` from a vertex `a` outside the goal zone to the `goal` can be shortened to a walk that
enters the goal zone *exactly once* and then proceeds to the goal for free.  Concretely, there is a
prefix `P : a ⤳ u` lying *entirely outside* the goal zone, a single boundary-crossing edge `(u, v)`
(`u ∉ goal_zone`, `v ∈ goal_zone`, recorded in `edges_entering_goal_zone`), and a *zero-cost* walk
`T : v ⤳ goal` inside the goal zone, with

  `P.cost + edgeCost (u,v) ≤ W.cost`.

The reason is exactly that once the goal zone is first entered the goal is reachable at no cost
(`v ∈ goal_zone` gives the free tail `T`), so whatever `W` does after its first crossing only adds
cost: re-leaving the goal zone never helps.  This is the single-crossing normal form underlying the
Helmert–Domshlak per-step bound.
-/
lemma exists_single_crossing_walk_le {V : Type} [FinEnum V] (g : NatGraph V) (goal : V)
    {a : V} (W : g.Walk a goal) (ha : a ∉ goal_zone g goal) :
    ∃ (u v : V) (adj : g.Adj u v) (P : g.Walk a u) (T : g.Walk v goal),
      (∀ x ∈ P.support, x ∉ goal_zone g goal) ∧
      u ∉ goal_zone g goal ∧
      v ∈ goal_zone g goal ∧
      (u, v) ∈ edges_entering_goal_zone g goal ∧
      T.cost = 0 ∧
      P.cost + g.edgeCost adj ≤ W.cost := by
  induction' W with u us ug W'
  · exact False.elim <| ha <| goal_mem_goal_zone g u
  · by_cases h : ug ∈ goal_zone g W'
    · refine' ⟨ us, ug, by assumption, WeightedDiGraph.Walk.nil, _ ⟩
      simp_all [ WeightedDiGraph.Walk.cost, WeightedDiGraph.Walk.support ]
      exact ⟨ mem_edges_entering_goal_zone g W' ha h ‹_›, by exact walk_of_zero_cost_reachable g ( by rw [ mem_goal_zone_iff ] at h; exact h ) ⟩
    · rename_i h₁ h₂ h₃
      obtain ⟨ u, v, adj, P, T, hP, hu, hv, huv, hT, hP' ⟩ := h₃ h
      use u, v, adj, WeightedDiGraph.Walk.cons h₁ P, T
      simp_all [ WeightedDiGraph.Walk.support, WeightedDiGraph.Walk.cost ]
      linarith

/-! ### Shortest-walk distance in a `NatGraph`

`graphDist g src f` is the minimum cost of a walk from `src` to `f` in `g`, taken as a value in
`WithTop ℕ = ℕ∞` (so it is `⊤` exactly when `f` is unreachable from `src`).  It is the natural
post-fixpoint object for `h^max`-style Bellman inequalities: it is bounded above by every walk cost
(`graphDist_le_walk`) and satisfies the per-edge triangle inequality (`graphDist_edge_le`). -/
noncomputable def graphDist {V : Type} [FinEnum V] (g : NatGraph V) (src f : V) : WithTop ℕ :=
  ⨅ W : g.Walk src f, (W.cost : WithTop ℕ)

/-- `graphDist` is bounded above by the cost of any concrete walk. -/
lemma graphDist_le_walk {V : Type} [FinEnum V] (g : NatGraph V) {src f : V}
    (W : g.Walk src f) : graphDist g src f ≤ (W.cost : WithTop ℕ) := by
  exact iInf_le (fun W : g.Walk src f => (W.cost : WithTop ℕ)) W

/-- The distance from a vertex to itself is `0`. -/
lemma graphDist_self {V : Type} [FinEnum V] (g : NatGraph V) (src : V) :
    graphDist g src src = 0 := by
  refine le_antisymm ?_ (by simp)
  simpa using graphDist_le_walk g (WeightedDiGraph.Walk.nil : g.Walk src src)

/-
**Triangle inequality along an edge.**  If `q → f` is an edge then the distance to `f` is at
most the distance to `q` plus the edge cost.
-/
lemma graphDist_edge_le {V : Type} [FinEnum V] (g : NatGraph V) {src q f : V}
    (adj : g.Adj q f) :
    graphDist g src f ≤ graphDist g src q + (g.edgeCost adj : WithTop ℕ) := by
  have h_walk : ∀ W : g.Walk src q, graphDist g src f ≤ (W.cost : WithTop ℕ) + (NatGraph.edgeCost adj : WithTop ℕ) := by
    intro W
    have h_walk : graphDist g src f ≤ (WeightedDiGraph.Walk.concat W adj).cost := by
      exact graphDist_le_walk g ( W.concat adj )
    convert h_walk using 1 ; norm_cast ; simp [ WeightedDiGraph.Walk.concat_inc_cost_by_edge ] ; ring!
  contrapose! h_walk
  obtain ⟨W, hW⟩ : ∃ W : g.Walk src q, (W.cost : WithTop ℕ) < graphDist g src f - (NatGraph.edgeCost adj : WithTop ℕ) := by
    have h_inf : graphDist g src q < graphDist g src f - (NatGraph.edgeCost adj : WithTop ℕ) := by
      convert lt_tsub_iff_right.mpr h_walk using 1
    contrapose! h_inf
    exact le_iInf fun W => h_inf W
  rw [ lt_tsub_iff_right ] at hW
  apply Exists.intro
  · exact hW

/-- Every walk cost is at least the distance — restated as a lower bound usable with `WithTop`. -/
lemma le_graphDist_iff {V : Type} [FinEnum V] (g : NatGraph V) {src f : V} (c : WithTop ℕ) :
    c ≤ graphDist g src f ↔ ∀ W : g.Walk src f, c ≤ (W.cost : WithTop ℕ) := by
  exact le_iInf_iff

/-
The justification-graph payload of an edge is at most the cost of any action witnessing that
edge (chosen precondition `f`, add effect containing `t`).
-/
lemma justification_graph_payload_le_cost {n : ℕ} (prob : STRIPS n)
    (pcf : precondition_choice_function prob) {f t : Fin n}
    (adj : (justification_graph prob pcf).Adj f t)
    (a0 : {b : Action n // b ∈ prob.actions'}) (hf : f = (↑(pcf a0) : Fin n))
    (ht : t ∈ a0.val.add'.val.toFinset) :
    (justification_graph prob pcf).Payload f t adj ≤ a0.val.cost := by
      convert List.min_le_of_mem _
      · infer_instance
      · infer_instance
      · grind +qlia

lemma cost_goal_zone_landmark_of_justification_graph {n : ℕ} (prob : STRIPS n)
    (u_i : unitary_init prob)
    (u_g : unitary_goal prob)
    (pcf : precondition_choice_function prob):
    ¬ zero_cost_reachable (justification_graph prob pcf) (get_unitary_init prob u_i) (get_unitary_goal prob u_g) →
    ∀ a ∈ (landmark_induced_by_cut prob (edges_entering_goal_zone (justification_graph prob pcf) (get_unitary_goal prob u_g)) pcf), a.cost > 0 := by
      intro h a ha
      obtain ⟨ft, hmem, ha⟩ : ∃ ft, ft ∈ edges_entering_goal_zone (justification_graph prob pcf) (get_unitary_goal prob u_g) ∧ a ∈ (prob.actions'.attach.filter (fun a => decide (ft.1 = (↑(pcf a) : Fin n) ∧ ft.2 ∈ a.val.add'.val.toFinset))).map (·.val) := by
        exact exists_of_mem_flatMap ha
      rw [ List.mem_map ] at ha
      obtain ⟨a0, ha0, rfl⟩ := ha
      rw [ List.mem_filter ] at ha0
      have hf : ft.1 = (↑(pcf a0) : Fin n) := by
        grind +splitIndPred
      have ht : ft.2 ∈ a0.val.add'.val.toFinset := by
        grind
      have hpay : (justification_graph prob pcf).Payload ft.1 ft.2 (edges_entering_goal_zone_are_edges (justification_graph prob pcf) (get_unitary_goal prob u_g) ft hmem) ≠ 0 := by
        exact edges_entering_goal_zone_dont_contain_zero_cost ( justification_graph prob pcf ) ( get_unitary_goal prob u_g ) ft hmem
      have hle : (justification_graph prob pcf).Payload ft.1 ft.2 (edges_entering_goal_zone_are_edges (justification_graph prob pcf) (get_unitary_goal prob u_g) ft hmem) ≤ a0.val.cost := by
        convert justification_graph_payload_le_cost prob pcf _ a0 hf ht using 1
      grind

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

    -- We charge `minCost` on the *relax-equivalence closure* of the cut-induced landmark, not on
    -- the landmark itself.  The closure is a *genuine* disjunctive action landmark of `prob`
    -- (`delete_relaxation_landmarks_are_landmarks`) for any precondition-choice function, which is
    -- exactly what makes the resulting cost partitioning admissible without any extra invariant on
    -- `pcf`.  All closure actions share a cost with some landmark action, so they cost at least
    -- `minCost`; hence the partitioning is valid.
    let lm' := get_all_equiv_delete_relaxed_actions prob lm
    let part : cost_partitioning prob 2 := fun p =>
      match p with
      | 0 => fun a_index => if prob.actions'[a_index] ∈ lm' then minCost else 0
      | 1 => fun a_index => if prob.actions'[a_index] ∈ lm' then prob.actions'[a_index].cost - minCost else prob.actions'[a_index].cost

    (lm,minCost,part)



/- The original statement of `lmcut_step_yields_landmark` lacked any reachability hypothesis:

theorem lmcut_step_yields_landmark {n : ℕ} (prob : STRIPS n)
    (u_i : unitary_init prob) (u_g : unitary_goal prob)
    (pcf : precondition_choice_function prob):
    is_delete_relaxed_disjunctive_action_landmark_for_state prob (lmcut_step prob u_g pcf).1 prob.init'

Since `(lmcut_step prob u_g pcf).1` is exactly the landmark induced by the edges entering the goal
zone, this is **false** without a reachability assumption, for the same reason as
`goal_zone_landmark_of_justification_graph` (a zero-cost path from init to goal yields an empty
landmark together with an existing delete-relaxed plan).  The faithful statement adds
`¬ zero_cost_reachable …`. -/
theorem lmcut_step_yields_landmark {n : ℕ} (prob : STRIPS n)
    (u_i : unitary_init prob)
    (u_g : unitary_goal prob)
    (pcf : precondition_choice_function prob)
    (i_g_not_zero_reachable : ¬ zero_cost_reachable (justification_graph prob pcf)
      (get_unitary_init prob u_i) (get_unitary_goal prob u_g)) :
    is_delete_relaxed_disjunctive_action_landmark_for_state prob (lmcut_step prob u_g pcf).1 prob.init' :=
  goal_zone_landmark_of_justification_graph prob u_i u_g pcf i_g_not_zero_reachable

theorem lmcut_step_yields_partitioning {n : ℕ} (prob : STRIPS n)
    (u_i : unitary_init prob)
    (u_g : unitary_goal prob)
    (pcf : precondition_choice_function prob):
    is_valid_cost_partitioning prob 2 (lmcut_step prob u_g pcf).2.2 := by
      intro a_index
      unfold lmcut_step
      by_cases h : prob.actions'[a_index] ∈ get_all_equiv_delete_relaxed_actions prob (landmark_induced_by_cut prob (edges_entering_goal_zone (justification_graph prob pcf) (get_unitary_goal prob u_g)) pcf)
      · simp [ List.finRange ]
        split_ifs <;> norm_num
        rw [ Nat.add_sub_of_le ]
        have := cost_eq_of_mem_get_all_equiv prob ( landmark_induced_by_cut prob ( edges_entering_goal_zone ( justification_graph prob pcf ) ( get_unitary_goal prob u_g ) ) pcf ) h
        obtain ⟨ l, hl₁, hl₂ ⟩ := this
        convert List.min_le_of_mem _
        · infer_instance
        · infer_instance
        · exact List.mem_map.mpr ⟨ l, hl₁, hl₂ ▸ rfl ⟩
      · simp [ List.finRange ]
        grind

/-
**Paper (Theorem 5, condition (a) companion).**  Every edge entering the goal zone — i.e. every
cut edge — costs at least the cut value `minCost := (lmcut_step prob u_g pcf).2.1`.

In the paper, `cmin := min_{o ∈ L} cost(o)` is the minimum cost of a cut operator, so each cut
operator (and hence each cut edge, whose payload is the cheapest witnessing action) costs at least
`cmin`.  Here the actions witnessing the edge `(u, v)` are a sublist of the cut-induced landmark
`lm`, and `minCost` is the minimum cost over all of `lm`, so the minimum over the witnesses (the
payload) is at least `minCost`.
-/
lemma minCost_le_cut_edge_payload {n : ℕ} (prob : STRIPS n)
    (u_g : unitary_goal prob) (pcf : precondition_choice_function prob)
    {u v : Fin n} (adj : (justification_graph prob pcf).Adj u v)
    (hmem : (u, v) ∈ edges_entering_goal_zone (justification_graph prob pcf)
      (get_unitary_goal prob u_g)) :
    (lmcut_step prob u_g pcf).2.1 ≤ (justification_graph prob pcf).Payload u v adj := by
  -- If the landmark list is empty, then the cost is zero, and since the payload is a natural number, it's always non-negative.
  by_cases h_empty : (landmark_induced_by_cut prob (edges_entering_goal_zone (justification_graph prob pcf) (get_unitary_goal prob u_g)) pcf) = []
  · unfold lmcut_step
    simp_all only [↓reduceDIte, zero_le]
  · unfold lmcut_step; simp [ h_empty ]
    obtain ⟨a, ha⟩ : ∃ a ∈ (landmark_induced_by_cut prob (edges_entering_goal_zone (justification_graph prob pcf) (get_unitary_goal prob u_g)) pcf), a.cost = (justification_graph prob pcf).Payload u v adj := by
      have h_edgeActions_subset_lm : (prob.actions'.attach.filter (fun a => decide (u = (↑(pcf a) : Fin n) ∧ v ∈ a.val.add'.val.toFinset))).map (·.val) ⊆ (landmark_induced_by_cut prob (edges_entering_goal_zone (justification_graph prob pcf) (get_unitary_goal prob u_g)) pcf) := by
        unfold landmark_induced_by_cut; simp [ List.subset_def ]
        grind
      have h_payload_in_lm : (justification_graph prob pcf).Payload u v adj ∈ (prob.actions'.attach.filter (fun a => decide (u = (↑(pcf a) : Fin n) ∧ v ∈ a.val.add'.val.toFinset))).map (fun a => a.val.cost) := by
        have h_payload_in_lm : (justification_graph prob pcf).Payload u v adj = (List.map (fun a => a.val.cost) (prob.actions'.attach.filter (fun a => decide (u = (↑(pcf a) : Fin n) ∧ v ∈ a.val.add'.val.toFinset)))).min (by
        obtain ⟨ a, ha ⟩ := adj
        exact List.ne_nil_of_mem ( List.mem_map.mpr ⟨ a, List.mem_filter.mpr ⟨ List.mem_attach _ _, by simpa using ha ⟩, rfl ⟩ )) := by
          unfold justification_graph
          simp_all only [mem_toFinset, Bool.decide_and, map_subtype, map_id_fun', id_eq]
        exact h_payload_in_lm.symm ▸ List.min_mem _
      grind
    exact ha.2 ▸ List.min_le_of_mem ( List.mem_map.mpr ⟨ a, ha.1, rfl ⟩ )

/-
The statement `lmcut_step_yields_landmark_with_heuristic_in_partition` (preserved below in a
comment) is **false** as written:

theorem lmcut_step_yields_landmark_with_heuristic_in_partition {n : ℕ} (prob : STRIPS n)
    (u_i : unitary_init prob) (u_g : unitary_goal prob)
    (pcf : precondition_choice_function prob)
    (i_g_reachable : reachable (justification_graph prob pcf) (get_unitary_init prob u_i) (get_unitary_goal prob u_g)) :
    (lmcut_step prob u_g pcf).2.1 =
      elementary_landmark_heuristic (partition_STRIPS prob (lmcut_step prob u_g pcf).2.2 ⟨0, by omega⟩) (lmcut_step prob u_g pcf).1 prob.init'

The right-hand side is `elementary_landmark_heuristic prob' lm prob.init'` where
`prob' = partition_STRIPS prob _ 0` and `lm = (lmcut_step prob u_g pcf).1`.  `elementary_landmark_heuristic`
first checks `is_disjunctive_action_landmark_for_state prob' lm prob.init'`, whose first conjunct is
`lm.all (fun a => decide (a ∈ prob'.actions))`.  But the actions in `lm` carry their *original* costs,
whereas `partition_STRIPS prob _ 0` rewrites every action's cost to the partition-`0` value
(`minCost` for landmark actions, `0` otherwise).  Since `Action`'s `DecidableEq` includes `cost`, a
landmark action whose original cost differs from `minCost` is **not** an element of `prob'.actions`,
so the conjunct (and hence the landmark check) fails and the right-hand side collapses to `0`,
while the left-hand side `(lmcut_step …).2.1 = minCost` is positive whenever the goal is reachable
but not zero-cost reachable.  (Even when all landmark costs happen to equal `minCost`, the second
conjunct still requires `lm` to be a *non-relaxed* landmark of `prob'`, which an `lmcut` landmark —
being only a delete-relaxed landmark — need not be.)  The lemma is therefore left unproven; a faithful
version would either evaluate `elementary_landmark_heuristic` against the delete relaxation or use the
equivalence-closure landmark `get_all_equiv_delete_relaxed_actions`.

A faithful version of the lemma is proved below
(`lmcut_step_yields_landmark_with_heuristic_in_partition`), and crucially it needs **no** invariant
on the pcf.  Two changes fix both problems above:

* the landmark's actions are mapped with `adapt_cost_of_action_to_partition`, so their costs become
  the partition-`0` costs and they are genuine actions of the partitioned problem (fixing the cost
  mismatch)
* the landmark used is the *relax-equivalence closure* `get_all_equiv_delete_relaxed_actions prob
  (lmcut_step …).1` of the cut-induced landmark.  `lmcut_step` charges `minCost` exactly on this
  closure.  The closure is a *genuine* (non-relaxed) disjunctive action landmark of `prob` for
  **any** pcf, because it contains *every* action of `prob` that is delete-relaxation equivalent to
  a cut-induced landmark action (`delete_relaxation_landmarks_are_landmarks`); whichever action a
  real plan actually uses, its relaxation matches a landmark action, hence the action itself lies in
  the closure.

This is why the earlier `relax_invariant_pcf prob pcf` hypothesis is no longer required: instead of
closing a single fixed landmark under the equivalence *via* the pcf, we charge the whole
equivalence class directly.  The cost is unchanged (all closure actions share a cost with some
landmark action, and `minCost` is the minimum landmark cost), and the partitioning stays valid.
-/
/-- The *relax-equivalence closure* of the landmark produced by `lmcut_step` is a *genuine*
(non-relaxed) disjunctive action landmark of `prob`, for **any** precondition-choice function.  No
`relax_invariant_pcf` hypothesis is needed: the cut induces a delete-relaxed landmark
(`lmcut_step_yields_landmark`), and closing it under delete-relaxation equivalence
(`delete_relaxation_landmarks_are_landmarks`) turns it into a genuine one — the closure contains
*every* action of `prob` that is delete-relaxation equivalent to a landmark action, so whichever
action a real plan actually uses is captured. -/
lemma lmcut_closure_is_genuine {n : ℕ} (prob : STRIPS n)
    (u_i : unitary_init prob) (u_g : unitary_goal prob)
    (pcf : precondition_choice_function prob)
    (i_g_not_zero_reachable : ¬ zero_cost_reachable (justification_graph prob pcf)
      (get_unitary_init prob u_i) (get_unitary_goal prob u_g)) :
    is_disjunctive_action_landmark_for_state prob
      (get_all_equiv_delete_relaxed_actions prob (lmcut_step prob u_g pcf).1) prob.init' := by
  apply delete_relaxation_landmarks_are_landmarks prob (lmcut_step prob u_g pcf).1 ?_ prob.init'
  · exact lmcut_step_yields_landmark prob u_i u_g pcf i_g_not_zero_reachable
  · rw [List.all_eq_true]
    intro a ha
    simpa [STRIPS.actions] using landmark_subset_actions prob _ pcf a ha

/-
Transfer a plan of a cost-partitioned problem to a plan of the original problem, recording for
each action used in the recovered plan its index in `prob.actions'` and the matching (cost-adapted)
action in the partitioned plan.  This works because `partition_STRIPS` only relabels costs, leaving
applicability and successor states unchanged.
-/
lemma path_partition_to_orig {n P : ℕ} (prob : STRIPS n) (partitioning : cost_partitioning prob P)
    (p : Fin P) {s1 s2 : State n} (path' : Path (partition_STRIPS prob partitioning p) s1 s2) :
    ∃ path : Path prob s1 s2,
      ∀ a0 ∈ path.actionsUsed, ∃ (i : Fin prob.actions'.length),
        prob.actions'[i] = a0 ∧
        Action.mk a0.name a0.pre' a0.add' a0.del' (partitioning p i) ∈ path'.actionsUsed := by
  induction' path' with a s2 ha succ π ih
  · exact ⟨ Path.empty a, by simp [ Path.actionsUsed ] ⟩
  · rename_i h₁ h₂ h₃
    obtain ⟨ i, hi ⟩ := List.mem_iff_getElem.mp ( show s2 ∈ (partition_STRIPS prob partitioning p).actions' from by simpa [ STRIPS.actions ] using ih )
    unfold partition_STRIPS at hi; simp_all [ List.getElem_mapFinIdx ]
    obtain ⟨ h, rfl ⟩ := hi
    use Path.cons (prob.actions'[i]) succ (by
    exact List.mem_toFinset.mpr ( List.getElem_mem _ )) h₁ h₃.choose
    intro a0 ha0; cases' List.mem_cons.mp ha0 with ha0 ha0 <;> simp_all [ Path.actionsUsed ]
    · exact ⟨ ⟨ i, h ⟩, rfl, Or.inl rfl ⟩
    · exact h₃.choose_spec a0 ha0 |> fun ⟨ i, hi ⟩ => ⟨ i, hi.1, Or.inr hi.2 ⟩

/-
A genuine disjunctive action landmark of `prob` transfers, via cost adaptation, to a genuine
disjunctive action landmark of any cost-partitioned problem, provided the partition assigns equal
costs to equal actions.
-/
lemma genuine_landmark_partition_transfer {n P : ℕ} (prob : STRIPS n)
    (partitioning : cost_partitioning prob P) (p : Fin P) (lm : List (Action n))
    (hlm : ∀ a ∈ lm, a ∈ prob.actions')
    (hpart : ∀ (i j : Fin prob.actions'.length), prob.actions'[i] = prob.actions'[j] →
      partitioning p i = partitioning p j)
    (h : is_disjunctive_action_landmark_for_state prob lm prob.init') :
    is_disjunctive_action_landmark_for_state (partition_STRIPS prob partitioning p)
      (lm.map (adapt_cost_of_action_to_partition prob partitioning p)) prob.init' := by
  refine' ⟨ _, _ ⟩
  · simp [ List.all_eq_true, STRIPS.actions ]
    exact fun x hx => adapt_cost_of_action_to_partition_mem prob partitioning p x (hlm x hx)
  · intro plan
    obtain ⟨path, hpath⟩ := path_partition_to_orig prob partitioning p plan.path
    obtain ⟨a0, ha0⟩ : ∃ a0 ∈ lm, a0 ∈ path.actionsUsed := by
      have := h.2 ⟨ plan.last, path, plan.goal ⟩
      simp_all only [Fin.getElem_fin]
      obtain ⟨w, h_1⟩ := this
      obtain ⟨left, right⟩ := h_1
      apply Exists.intro
      · apply And.intro
        on_goal 2 => exact right
        · simp_all only
    obtain ⟨ i, hi, hi' ⟩ := hpath a0 ha0.2
    use Action.mk a0.name a0.pre' a0.add' a0.del' (partitioning p i)
    refine' ⟨ _, _ ⟩
    · unfold adapt_cost_of_action_to_partition; simp
      grind
    · exact hi'

theorem lmcut_step_yields_non_zero_heuristic {n : ℕ} (prob : STRIPS n)
    (u_i : unitary_init prob)
    (u_g : unitary_goal prob)
    (pcf : precondition_choice_function prob)
    (i_g_reachable : reachable (justification_graph prob pcf) (get_unitary_init prob u_i) (get_unitary_goal prob u_g))
    (i_g_not_zero_reachable : ¬ zero_cost_reachable (justification_graph prob pcf) (get_unitary_init prob u_i) (get_unitary_goal prob u_g)) :
    (lmcut_step prob u_g pcf).2.1 > 0 := by
      unfold lmcut_step at *; simp [ * ] at *
      split_ifs
      · rename_i h
        obtain ⟨ft, hft⟩ : ∃ ft, ft ∈ edges_entering_goal_zone (justification_graph prob pcf) (get_unitary_goal prob u_g) := by
          obtain ⟨w, hw⟩ : ∃ w : (justification_graph prob pcf).Walk (get_unitary_init prob u_i) (get_unitary_goal prob u_g), True := by
            exact ⟨ walk_of_reachable _ i_g_reachable |> Classical.choice, trivial ⟩
          have h_nonempty : get_unitary_init prob u_i ∉ goal_zone (justification_graph prob pcf) (get_unitary_goal prob u_g) := by
            rw [ mem_goal_zone_iff ]
            simp_all only [Bool.false_eq_true, not_false_eq_true]
          exact List.exists_mem_of_ne_nil _ ( edges_entering_goal_zone_nonempty _ _ w ( goal_mem_goal_zone _ _ ) h_nonempty )
        obtain ⟨a0, ha0⟩ : ∃ a0 : {b : Action n // b ∈ prob.actions'}, ft.1 = (↑(pcf a0) : Fin n) ∧ ft.2 ∈ a0.val.add'.val.toFinset := by
          have := edges_entering_goal_zone_are_edges (justification_graph prob pcf) (get_unitary_goal prob u_g) ft hft
          unfold justification_graph at this
          simp_all only [mem_toFinset, Subtype.exists, exists_and_right]
        exact absurd h ( by exact List.ne_nil_of_mem ( mem_landmark_induced prob ( edges_entering_goal_zone ( justification_graph prob pcf ) ( get_unitary_goal prob u_g ) ) pcf a0 ft.1 ft.2 hft ha0.1 ha0.2 ) )
      · obtain ⟨a, ha⟩ : ∃ a ∈ landmark_induced_by_cut prob (edges_entering_goal_zone (justification_graph prob pcf) (get_unitary_goal prob u_g)) pcf, a.cost = (map (fun a => a.cost) (landmark_induced_by_cut prob (edges_entering_goal_zone (justification_graph prob pcf) (get_unitary_goal prob u_g)) pcf)).min (by simp_all [ List.map_eq_nil_iff, ne_eq ]) := by
          convert min_map _ _ _
        exact ha.2 ▸ cost_goal_zone_landmark_of_justification_graph prob u_i u_g pcf
          ( by simp_all only [Bool.false_eq_true, not_false_eq_true] ) a ha.1

/-
A positive step value forces a nonempty landmark.
-/
private lemma lmcut_step_landmark_ne_nil {n : ℕ} (prob : STRIPS n)
    (u_g : unitary_goal prob) (pcf : precondition_choice_function prob)
    (hpos : 0 < (lmcut_step prob u_g pcf).2.1) : (lmcut_step prob u_g pcf).1 ≠ [] := by
  contrapose! hpos; unfold lmcut_step at *; simp_all

/-
The step value `minCost` is a lower bound on the cost of every action of the cut-induced
landmark (it is, by definition, the minimum of their costs).
-/
private lemma lmcut_step_value_le_cost_of_mem {n : ℕ} (prob : STRIPS n) (u_g : unitary_goal prob)
    (pcf : precondition_choice_function prob) {a : Action n}
    (ha : a ∈ (lmcut_step prob u_g pcf).1) : (lmcut_step prob u_g pcf).2.1 ≤ a.cost := by
  unfold lmcut_step at *; simp at *
  split_ifs
  · exact Nat.zero_le _
  · convert List.min_le_of_mem _
    · infer_instance
    · infer_instance
    · exact List.mem_map.mpr ⟨ a, ha, rfl ⟩

/-- A nonempty list all of whose elements equal `c` has minimum `c`. -/
private lemma list_min_const (l : List ℕ) (c : ℕ) (h : l ≠ []) (hc : ∀ x ∈ l, x = c) :
    l.min h = c := by
  refine le_antisymm ?_ ?_
  · obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil l h
    exact le_of_le_of_eq (List.min_le_of_mem ha) (hc a ha)
  · exact le_of_eq (hc _ (List.min_mem (l := l) h)).symm

/-
The partition-`0` cost of `lmcut_step` depends only on the action (not on its index): equal
actions get equal costs.
-/
private lemma lmcut_part0_action_invariant {n : ℕ} (prob : STRIPS n) (u_g : unitary_goal prob)
    (pcf : precondition_choice_function prob) (i j : Fin prob.actions'.length)
    (hij : prob.actions'[i] = prob.actions'[j]) :
    (lmcut_step prob u_g pcf).2.2 ⟨0, by omega⟩ i
      = (lmcut_step prob u_g pcf).2.2 ⟨0, by omega⟩ j := by
  unfold lmcut_step
  grind +splitIndPred

/-
Every action of the relax-equivalence closure of the `lmcut_step` landmark, after adapting its cost
to partition `0`, has cost equal to the step's value `minCost` (partition `0` charges `minCost`
exactly to the closure actions).
-/
private lemma lmcut_adapt_cost_eq {n : ℕ} (prob : STRIPS n) (u_g : unitary_goal prob)
    (pcf : precondition_choice_function prob) (a : Action n)
    (ha : a ∈ get_all_equiv_delete_relaxed_actions prob (lmcut_step prob u_g pcf).1) :
    (adapt_cost_of_action_to_partition prob (lmcut_step prob u_g pcf).2.2 ⟨0, by omega⟩ a).cost
      = (lmcut_step prob u_g pcf).2.1 := by
  unfold lmcut_step at *; simp at *
  unfold adapt_cost_of_action_to_partition; simp
  grind +suggestions

/-- Faithful version of the critical lemma: the value `(lmcut_step …).2.1 = minCost` computed by one
landmark-cutting step equals the elementary landmark heuristic of the partition-`0` problem, where
the landmark is the step's landmark with its action costs adapted to partition `0` (via
`adapt_cost_of_action_to_partition`).  Adapting the costs makes the landmark actions genuine actions
of the partitioned problem and gives them all cost `minCost`; relax invariance of the pcf makes the
landmark a genuine (non-relaxed) landmark, so the heuristic evaluates to `minCost`. -/
theorem lmcut_step_yields_landmark_with_heuristic_in_partition {n : ℕ} (prob : STRIPS n)
    (u_i : unitary_init prob) (u_g : unitary_goal prob)
    (pcf : precondition_choice_function prob)
    (i_g_reachable : reachable (justification_graph prob pcf)
      (get_unitary_init prob u_i) (get_unitary_goal prob u_g))
    (i_g_not_zero_reachable : ¬ zero_cost_reachable (justification_graph prob pcf)
      (get_unitary_init prob u_i) (get_unitary_goal prob u_g)) :
    (lmcut_step prob u_g pcf).2.1 =
      elementary_landmark_heuristic
        (partition_STRIPS prob (lmcut_step prob u_g pcf).2.2 ⟨0, by omega⟩)
        ((get_all_equiv_delete_relaxed_actions prob (lmcut_step prob u_g pcf).1).map
          (adapt_cost_of_action_to_partition prob (lmcut_step prob u_g pcf).2.2 ⟨0, by omega⟩))
        prob.init' := by
  have hpos : 0 < (lmcut_step prob u_g pcf).2.1 :=
    lmcut_step_yields_non_zero_heuristic prob u_i u_g pcf i_g_reachable i_g_not_zero_reachable
  have hlm_ne : (lmcut_step prob u_g pcf).1 ≠ [] := lmcut_step_landmark_ne_nil prob u_g pcf hpos
  -- the closure is nonempty too (it contains the landmark)
  have hclo_ne : get_all_equiv_delete_relaxed_actions prob (lmcut_step prob u_g pcf).1 ≠ [] := by
    obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ hlm_ne
    have ha' : a ∈ prob.actions' := landmark_subset_actions prob _ pcf a ha
    exact List.ne_nil_of_mem (mem_get_all_equiv_of_mem prob _ ha ha')
  have hgen : is_disjunctive_action_landmark_for_state
      (partition_STRIPS prob (lmcut_step prob u_g pcf).2.2 ⟨0, by omega⟩)
      ((get_all_equiv_delete_relaxed_actions prob (lmcut_step prob u_g pcf).1).map
        (adapt_cost_of_action_to_partition prob (lmcut_step prob u_g pcf).2.2 ⟨0, by omega⟩))
      prob.init' := by
    apply genuine_landmark_partition_transfer prob (lmcut_step prob u_g pcf).2.2 ⟨0, by omega⟩
      (get_all_equiv_delete_relaxed_actions prob (lmcut_step prob u_g pcf).1)
    · intro a ha
      exact mem_actions_of_mem_get_all_equiv prob _ ha
    · intro i j hij; exact lmcut_part0_action_invariant prob u_g pcf i j hij
    · exact lmcut_closure_is_genuine prob u_i u_g pcf i_g_not_zero_reachable
  have hlm'_ne : (get_all_equiv_delete_relaxed_actions prob (lmcut_step prob u_g pcf).1).map
      (adapt_cost_of_action_to_partition prob (lmcut_step prob u_g pcf).2.2 ⟨0, by omega⟩) ≠ [] := by
    simpa using hclo_ne
  unfold elementary_landmark_heuristic
  rw [if_pos hgen, dif_neg hlm'_ne]
  symm
  apply list_min_const
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
  exact lmcut_adapt_cost_eq prob u_g pcf a ha

/-
The total action cost of `subprob = partition_STRIPS prob (lmcut_step …).2.2 1` is strictly
smaller than that of `prob`, provided the step's value `minCost` is positive: every landmark
action (there is at least one, since `minCost > 0` forces a nonempty landmark) has its cost in
partition `1` reduced by `minCost`, while no action's cost increases. This is the measure that
makes `lmcut_inner` terminate.
-/
lemma lmcut_step_subprob_sum_lt {n : ℕ} (prob : STRIPS n) (u_g : unitary_goal prob)
    (pcf : precondition_choice_function prob) (hpos : (lmcut_step prob u_g pcf).2.1 > 0) :
    ((partition_STRIPS prob (lmcut_step prob u_g pcf).2.2 ⟨1, by omega⟩).actions'.map
        (fun a => a.cost)).sum < (prob.actions'.map (fun a => a.cost)).sum := by
          -- Rewrite both sides as sums over action indices using `partition_STRIPS_cost_sum` and `actions_cost_sum_eq`.
          have h_sum_eq : ∑ i : Fin prob.actions'.length, (lmcut_step prob u_g pcf).2.2 ⟨1, by omega⟩ i < ∑ i : Fin prob.actions'.length, prob.actions'[i].cost := by
            refine' Finset.sum_lt_sum _ _
            · unfold lmcut_step
              intro i a
              simp_all only [gt_iff_lt, Finset.mem_univ, Fin.getElem_fin]
              split
              next h => simp_all only [tsub_le_iff_right, le_add_iff_nonneg_right, zero_le]
              next h => simp_all only [le_refl]
            · obtain ⟨a0, ha0⟩ : ∃ a0 ∈ (lmcut_step prob u_g pcf).1, a0.cost ≥ (lmcut_step prob u_g pcf).2.1 := by
                exact Exists.elim ( List.length_pos_iff_exists_mem.mp ( List.length_pos_iff.mpr ( lmcut_step_landmark_ne_nil prob u_g pcf hpos ) ) ) fun x hx => ⟨ x, hx, lmcut_step_value_le_cost_of_mem prob u_g pcf hx ⟩
              obtain ⟨i, hi⟩ : ∃ i : Fin prob.actions'.length, prob.actions'[i] = a0 ∧ a0 ∈ get_all_equiv_delete_relaxed_actions prob (lmcut_step prob u_g pcf).1 := by
                have h_mem : a0 ∈ prob.actions' := by
                  exact landmark_subset_actions prob _ pcf _ ha0.1
                exact ⟨ ⟨ List.idxOf a0 prob.actions', List.idxOf_lt_length_iff.mpr h_mem ⟩, by simp [ List.getElem_idxOf ], mem_get_all_equiv_of_mem prob _ ha0.1 h_mem ⟩
              unfold lmcut_step at *; simp at *
              grind
          convert h_sum_eq using 1
          · convert partition_STRIPS_cost_sum prob ( lmcut_step prob u_g pcf ).2.2 ⟨ 1, by omega ⟩ using 1
          · convert actions_cost_sum_eq prob

def lmcut_inner {n : ℕ} (prob : STRIPS n)
    (u_i : unitary_init prob)
    (u_g : unitary_goal prob)
    (hp : has_preconditions prob)
    (pcf : Π p : STRIPS n, has_preconditions p → precondition_choice_function p):
      List (List (Action n)) × ℕ × Σ p : ℕ, (cost_partitioning prob p) :=

    let jg := justification_graph prob (pcf prob hp)
    let i := (get_unitary_init prob u_i)
    let goal := (get_unitary_goal prob u_g)

    -- return no partitioning (`cost_partitioning prob 0` is the empty family)
    if ¬ reachable jg i goal then ([[]], (2 ^ n) * max_action_cost prob , ⟨0, fun p => p.elim0⟩)
    -- return no partitioning
    else if zero_cost_reachable jg i goal then ([], 0, ⟨0, fun p => p.elim0⟩)
    else
     let r := lmcut_step prob u_g (pcf prob hp)
     let subprob := partition_STRIPS prob r.2.2 ⟨1, by omega⟩

     let subret := lmcut_inner subprob u_i u_g
       (partition_STRIPS_has_preconditions prob r.2.2 ⟨1, by omega⟩ hp) pcf

     let lms : List (List (Action n)):= r.1 :: subret.1
     let hval : ℕ := r.2.1 + subret.2.1
     -- combine: partition `0` is the landmark partition computed by this step (`r.2.2 0`),
     -- the remaining partitions are the sub-partitioning found recursively for `subprob`
     -- (whose action list has the same length as `prob`'s, hence the `Fin.cast`).
     let parts : Σ p : ℕ, (cost_partitioning prob p) :=
       ⟨1 + subret.2.2.1, fun p a =>
         if h : (p : ℕ) = 0 then r.2.2 0 a
         else subret.2.2.2 ⟨(p : ℕ) - 1, by have := p.isLt; omega⟩
           (Fin.cast (partition_STRIPS_actions_length prob r.2.2 ⟨1, by omega⟩).symm a)⟩
     (lms, hval, parts)

termination_by (prob.actions'.map (fun a => a.cost)).sum -- decreases due to non-zero partitioning
decreasing_by
  all_goals (
    apply lmcut_step_subprob_sum_lt prob u_g (pcf prob hp)
    apply lmcut_step_yields_non_zero_heuristic prob u_i u_g (pcf prob hp)
    · change reachable jg i goal = true; exact not_not.mp (by assumption)
    · change ¬ zero_cost_reachable jg i goal = true; assumption)


/-! ### Helpers for `lmcut_inner_admissible_for_init`

The admissibility of the value returned by `lmcut_inner` for the initial state is obtained by
induction over the recursive structure of `lmcut_inner` (equivalently, strong induction on the total
action cost, the termination measure).  Each recursion step decomposes the problem into the
two-element cost partitioning `r.2.2` produced by `lmcut_step` (`r := lmcut_step prob u_g (pcf
prob)`); we charge the plan once through each partition:

* partition `0` carries the landmark, and the elementary landmark heuristic of partition `0` on the
  (cost-adapted) landmark equals the step value `r.2.1`
  (`lmcut_step_yields_landmark_with_heuristic_in_partition`); elementary landmark heuristics are
  admissible (`elementary_landmark_heuristic_is_admissible`), so the plan replayed in partition `0`
  costs at least `r.2.1`
* partition `1` is the recursive subproblem `subprob`, and the induction hypothesis bounds the plan
  replayed there by the recursively computed value
* validity of the partitioning (`lmcut_step_yields_partitioning`) means the two replayed plan costs
  sum to at most the real plan cost.

The unreachable base case is discharged because the problem then has no plan at all
(`lmcut_no_plan_of_not_reachable`). -/

/-- A walk in the edge-removed graph is in particular a walk in the original graph: removing
edges only restricts adjacency. -/
noncomputable def walk_of_remove_edges_walk {V E : Type} [FinEnum V] (g : WeightedDiGraph V E)
    (cut : List (V × V)) {u v : V} (w : (remove_edges g cut).Walk u v) : g.Walk u v := by
  induction w with
  | nil => exact WeightedDiGraph.Walk.nil
  | cons adj _ ih => exact WeightedDiGraph.Walk.cons adj.1 ih

/-- A walk witnesses reachability (`astar` is complete). -/
lemma reachable_of_walk {V : Type} [FinEnum V] (g : NatGraph V) {v goal : V}
    (w : g.Walk v goal) : reachable g v goal := by
  have hcomplete : (NatGraph.astar (g := g) (fun _ => 0) v goal).isSome := by
    apply NatGraph.astar_is_complete
    exact ⟨⟨w.bypass, WeightedDiGraph.Walk.bypass_isPath w⟩, rfl⟩
  unfold reachable
  cases h : NatGraph.astar (g := g) (fun _ => 0) v goal with
  | none => rw [h] at hcomplete; simp at hcomplete
  | some p => rfl

/-- If the unitary goal is not reachable from the unitary initial fact in the justification graph,
then the problem has no plan at all.  A real plan relaxes (via `relax_path`) to a delete-relaxed
path reaching the goal fact, and replaying that path in the justification graph
(`jgraph_reach_of_dr_path`, with the empty cut) witnesses reachability of the goal fact from the
initial fact — contradicting the assumption. -/
lemma lmcut_no_plan_of_not_reachable {n : ℕ} (prob : STRIPS n) (u_i : unitary_init prob)
    (u_g : unitary_goal prob) (pcf : precondition_choice_function prob)
    (h : ¬ reachable (justification_graph prob pcf)
      (get_unitary_init prob u_i) (get_unitary_goal prob u_g)) :
    IsEmpty (Plan prob prob.init) := by
  constructor
  intro plan
  apply h
  set i0 := get_unitary_init prob u_i with hi0
  set g0 := get_unitary_goal prob u_g with hg0
  obtain ⟨t2, ht2, q, hq⟩ := relax_path prob plan.path (le_refl prob.init)
  have Hwit : ∀ (a0 : {b : Action n // b ∈ prob.actions'}),
      delete_relax_action a0.val ∈ q.actionsUsed →
      ∀ y ∈ a0.val.add'.val.toFinset, ((↑(pcf a0) : Fin n), y) ∉ ([] : List (Fin n × Fin n)) := by
    intro a0 _ y _; simp
  have hinit : convertState prob.init' = ({i0} : Set (Fin n)) := get_unitary_init_is_init prob u_i
  have Hsrc : ∀ s ∈ (prob.init : State n),
      Nonempty ((remove_edges (justification_graph prob pcf) []).Walk i0 s) := by
    intro s hs
    rw [show (prob.init : State n) = convertState prob.init' from rfl, hinit,
      Set.mem_singleton_iff] at hs
    subst hs; exact ⟨WeightedDiGraph.Walk.nil⟩
  have hreach := jgraph_reach_of_dr_path prob pcf [] i0 q Hwit Hsrc
  have hg0last : g0 ∈ plan.last := by
    apply plan.goal
    show g0 ∈ convertVarSet prob.goal'
    unfold convertVarSet
    rw [get_unitary_goal_is_goal prob u_g]
    simp [hg0]
  obtain ⟨w⟩ := hreach g0 (ht2 hg0last)
  exact reachable_of_walk _ (walk_of_remove_edges_walk _ _ w)

/-- Replay a path of `prob` in a cost-partitioned problem `partition_STRIPS prob partitioning p`.
Since partitioning only relabels action costs (applicability and successors are unchanged), the same
sequence of cost-adapted actions is a valid path, and its used actions are exactly the original ones
adapted to the partition. -/
lemma path_transfer_to_partition {n P : ℕ} (prob : STRIPS n)
    (partitioning : cost_partitioning prob P) (p : Fin P)
    {s1 s2 : State n} (path : Path prob s1 s2) :
    ∃ path' : Path (partition_STRIPS prob partitioning p) s1 s2,
      path'.actionsUsed
        = path.actionsUsed.map (adapt_cost_of_action_to_partition prob partitioning p) := by
  induction path with
  | empty s => exact ⟨Path.empty s, rfl⟩
  | cons a m ha succ π ih =>
    obtain ⟨π', hπ'⟩ := ih
    have ha' : a ∈ prob.actions' := by simpa [STRIPS.actions] using ha
    obtain ⟨_, hpre, hadd, hdel⟩ := adapt_cost_of_action_to_partition_fields prob partitioning p a
    have hmem : adapt_cost_of_action_to_partition prob partitioning p a
        ∈ (partition_STRIPS prob partitioning p).actions := by
      simpa [STRIPS.actions] using adapt_cost_of_action_to_partition_mem prob partitioning p a ha'
    have hpre' : (adapt_cost_of_action_to_partition prob partitioning p a).pre = a.pre := by
      unfold Action.pre; rw [hpre]
    have hadd' : (adapt_cost_of_action_to_partition prob partitioning p a).add = a.add := by
      unfold Action.add; rw [hadd]
    have hdel' : (adapt_cost_of_action_to_partition prob partitioning p a).del = a.del := by
      unfold Action.del; rw [hdel]
    refine ⟨Path.cons (adapt_cost_of_action_to_partition prob partitioning p a) m hmem ?_ π', ?_⟩
    · unfold Successor Applicable
      rw [hpre', hadd', hdel']
      exact succ
    · simp [Path.actionsUsed, hπ']

/-- A plan of `prob` (for the initial state) replays in any partition; its cost there is the sum of
the partition's costs of the actions it uses. -/
lemma plan_transfer_to_partition {n P : ℕ} (prob : STRIPS n)
    (partitioning : cost_partitioning prob P) (p : Fin P)
    (plan : Plan prob prob.init) :
    ∃ plan' : Plan (partition_STRIPS prob partitioning p)
        (partition_STRIPS prob partitioning p).init,
      plan'.path.cost = (plan.path.actionsUsed.map
        (fun a => (adapt_cost_of_action_to_partition prob partitioning p a).cost)).sum := by
  obtain ⟨path', hpath'⟩ := path_transfer_to_partition prob partitioning p plan.path
  refine ⟨⟨plan.last, path', plan.goal⟩, ?_⟩
  rw [path_cost_eq_sum_actionsUsed, hpath', List.map_map]
  rfl

/-- Pointwise-bounded sums of two cost functions over a list. -/
lemma list_sum_map_add_le {α : Type*} (L : List α) (f g h : α → ℕ)
    (hle : ∀ a ∈ L, f a + g a ≤ h a) :
    (L.map f).sum + (L.map g).sum ≤ (L.map h).sum := by
  induction L with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    have hat : f a + g a ≤ h a := hle a (List.mem_cons_self ..)
    have ht : (t.map f).sum + (t.map g).sum ≤ (t.map h).sum :=
      ih (fun x hx => hle x (List.mem_cons_of_mem _ hx))
    calc f a + (t.map f).sum + (g a + (t.map g).sum)
        = f a + g a + ((t.map f).sum + (t.map g).sum) := by ring
      _ ≤ h a + (t.map h).sum := Nat.add_le_add hat ht

/-- The value returned by `lmcut_inner` in the zero-cost-reachable branch is `0`. -/
lemma lmcut_inner_value_zero {n : ℕ} (prob : STRIPS n) (u_i : unitary_init prob)
    (u_g : unitary_goal prob) (hp : has_preconditions prob)
    (pcf : Π p : STRIPS n, has_preconditions p → precondition_choice_function p)
    (hr : reachable (justification_graph prob (pcf prob hp))
      (get_unitary_init prob u_i) (get_unitary_goal prob u_g))
    (hz : zero_cost_reachable (justification_graph prob (pcf prob hp))
      (get_unitary_init prob u_i) (get_unitary_goal prob u_g)) :
    (lmcut_inner prob u_i u_g hp pcf).2.1 = 0 := by
  rw [lmcut_inner]
  simp [hr, hz]

/-- The value returned by `lmcut_inner` in the recursive branch: the step value plus the value of
the recursive call on the subproblem. -/
lemma lmcut_inner_value_step {n : ℕ} (prob : STRIPS n) (u_i : unitary_init prob)
    (u_g : unitary_goal prob) (hp : has_preconditions prob)
    (pcf : Π p : STRIPS n, has_preconditions p → precondition_choice_function p)
    (hr : reachable (justification_graph prob (pcf prob hp))
      (get_unitary_init prob u_i) (get_unitary_goal prob u_g))
    (hz : ¬ zero_cost_reachable (justification_graph prob (pcf prob hp))
      (get_unitary_init prob u_i) (get_unitary_goal prob u_g)) :
    (lmcut_inner prob u_i u_g hp pcf).2.1
      = (lmcut_step prob u_g (pcf prob hp)).2.1
        + (lmcut_inner (partition_STRIPS prob (lmcut_step prob u_g (pcf prob hp)).2.2 ⟨1, by omega⟩)
            u_i u_g
            (partition_STRIPS_has_preconditions prob (lmcut_step prob u_g (pcf prob hp)).2.2
              ⟨1, by omega⟩ hp) pcf).2.1 := by
  rw [lmcut_inner]
  simp [hr, hz]

/-- Strong-induction skeleton for `lmcut_inner_admissible_for_init`. -/
lemma lmcut_inner_admissible_aux {n : ℕ}
    (pcf : Π p : STRIPS n, has_preconditions p → precondition_choice_function p) (M : ℕ) :
    ∀ (prob : STRIPS n) (u_i : unitary_init prob) (u_g : unitary_goal prob)
      (hp : has_preconditions prob),
      (prob.actions'.map (fun a => a.cost)).sum = M →
      ∀ plan : Plan prob prob.init, plan.path.cost ≥ (lmcut_inner prob u_i u_g hp pcf).2.1 := by
  induction M using Nat.strong_induction_on with
  | _ M IH =>
    intro prob u_i u_g hp hM plan
    by_cases hr : reachable (justification_graph prob (pcf prob hp))
        (get_unitary_init prob u_i) (get_unitary_goal prob u_g)
    · by_cases hz : zero_cost_reachable (justification_graph prob (pcf prob hp))
          (get_unitary_init prob u_i) (get_unitary_goal prob u_g)
      · rw [lmcut_inner_value_zero prob u_i u_g hp pcf hr hz]; exact Nat.zero_le _
      · -- recursive step: charge the plan through both partitions of `lmcut_step`
        set r := lmcut_step prob u_g (pcf prob hp) with hr_def
        set subprob := partition_STRIPS prob r.2.2 ⟨1, by omega⟩ with hsub_def
        rw [lmcut_inner_value_step prob u_i u_g hp pcf hr hz]
        -- replay the plan in partition 0 and partition 1
        obtain ⟨plan0, hplan0⟩ := plan_transfer_to_partition prob r.2.2 ⟨0, by omega⟩ plan
        obtain ⟨plan1, hplan1⟩ := plan_transfer_to_partition prob r.2.2 ⟨1, by omega⟩ plan
        -- partition 0: the step value is the elementary landmark heuristic, which is admissible
        have hstep := lmcut_step_yields_landmark_with_heuristic_in_partition prob u_i u_g (pcf prob hp)
          hr hz
        have h0 : r.2.1 ≤ plan0.path.cost := by
          have hadm := elementary_landmark_heuristic_is_admissible
            (partition_STRIPS prob r.2.2 ⟨0, by omega⟩)
            ((get_all_equiv_delete_relaxed_actions prob r.1).map
              (adapt_cost_of_action_to_partition prob r.2.2 ⟨0, by omega⟩)) prob.init' plan0
          rw [hstep]; exact hadm
        -- partition 1: induction hypothesis on the strictly smaller subproblem
        have hpos : 0 < r.2.1 := lmcut_step_yields_non_zero_heuristic prob u_i u_g (pcf prob hp) hr hz
        have hsub_lt : (subprob.actions'.map (fun a => a.cost)).sum < M := by
          rw [← hM]; exact lmcut_step_subprob_sum_lt prob u_g (pcf prob hp) hpos
        have h1 : (lmcut_inner subprob u_i u_g
            (partition_STRIPS_has_preconditions prob r.2.2 ⟨1, by omega⟩ hp) pcf).2.1
            ≤ plan1.path.cost :=
          IH _ hsub_lt subprob u_i u_g _ rfl plan1
        -- validity of the partitioning gives the cost split
        have hvalid := lmcut_step_yields_partitioning prob u_i u_g (pcf prob hp)
        have e2 : ∀ f : Fin 2 → ℕ, ((List.finRange 2).map f).sum = f 0 + f 1 := by
          intro f
          simp only [show List.finRange 2 = [0, 1] from rfl, List.map_cons, List.map_nil,
            List.sum_cons, List.sum_nil, add_zero]
        have hsplit : plan0.path.cost + plan1.path.cost ≤ plan.path.cost := by
          rw [hplan0, hplan1, path_cost_eq_sum_actionsUsed]
          apply list_sum_map_add_le
          intro a ha
          have hamem : a ∈ prob.actions' := by
            simpa [STRIPS.actions] using mem_actions_of_mem_actionsUsed plan.path ha
          have hidx : prob.actions'.idxOf a < prob.actions'.length :=
            List.idxOf_lt_length_of_mem hamem
          have hget : prob.actions'[(⟨prob.actions'.idxOf a, hidx⟩ : Fin prob.actions'.length)] = a :=
            List.getElem_idxOf hidx
          rw [adapt_cost_of_action_to_partition_cost prob r.2.2 ⟨0, by omega⟩ a hamem,
              adapt_cost_of_action_to_partition_cost prob r.2.2 ⟨1, by omega⟩ a hamem]
          have hv := hvalid ⟨prob.actions'.idxOf a, hidx⟩
          rw [e2, hget] at hv
          exact hv
        exact le_trans (Nat.add_le_add h0 h1) hsplit
    · exact ((lmcut_no_plan_of_not_reachable prob u_i u_g (pcf prob hp) hr).false plan).elim

/-- lmcut essentially returns a cost partioning over elementary landmark heuristics. Cost
partitioning preserves admissibility and elementary landmark heuristics are admissible, so
admissibility for init follows. Note that the `lmcut_inner` version does not yet take the actual
state into account, it computes an estimate only for init.

No invariant on the precondition-choice function is required.  Each step charges its value `minCost`
on the *relax-equivalence closure* of the cut-induced landmark, which is a *genuine* disjunctive
action landmark of the (partitioned) problem for **any** pcf (`lmcut_closure_is_genuine`,
`lmcut_step_yields_landmark_with_heuristic_in_partition`).  Hence the one-step cost-partitioning
decomposition `plan.cost = ∑ part1 + ∑ part0 ≥ subvalue + minCost` goes through by strong induction on
the total action cost, with the unreachable base case discharged because the problem then has no
plan (`lmcut_no_plan_of_not_reachable`). -/
lemma lmcut_inner_admissible_for_init {n : ℕ} (prob : STRIPS n)
    (u_i : unitary_init prob)
    (u_g : unitary_goal prob)
    (hp : has_preconditions prob)
    (pcf : Π p : STRIPS n, has_preconditions p → precondition_choice_function p):
      ∀ plan : Plan prob prob.init, plan.path.cost ≥ (lmcut_inner prob u_i u_g hp pcf).2.1 :=
  lmcut_inner_admissible_aux pcf _ prob u_i u_g hp rfl