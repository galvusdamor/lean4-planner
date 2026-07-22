import planning.Landmark
import planning.CostPartitioning
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Set.Card
import Mathlib

namespace STRIPS

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

def i_g_normal_form {n : ℕ} (prob : PlanningTask n) : PlanningTask (n+2) :=
  let emb : Fin n → Fin (n + 2) := Fin.castLE (by omega)
  let goal_pre : VarSet (n + 2) := VarSet.ofList (prob.goal'.toList.map emb)
       -- the current goal is the precondition of the goal action
  PlanningTask.mk
    (prob.varNames.append (⟨#["i","g"] , by rfl⟩))
    ((prob.actions'.map (fun a =>
      Action.mk  a.name
        (VarSet.ofList ((a.pre.toList.map emb) ++ [⟨n, by omega⟩]))
          -- every action gets n as an additional precondition
        (VarSet.ofList (a.add.toList.map emb))
        (VarSet.ofList (a.del.toList.map emb))
        a.cost
      )) ++
      [Action.mk
        "init"
        (singletonVarSet ⟨n, by omega⟩) -- pre is only init
        -- Corrected `add` effect: add exactly the embedded initial facts.
        (VarSet.ofList ((prob.init').toList.map emb))
        (∅ : VarSet (n+2)) -- no deletes
        0,
        Action.mk
        "goal"
        goal_pre
        (singletonVarSet ⟨n+1, by omega⟩) -- add is only goal
        (∅ : VarSet (n+2)) -- no deletes
        0
      ]
    )
    ⟨BitVec.zero (n+2) ||| (BitVec.twoPow (n+2) n)⟩ -- the initial state now contains only i
    (singletonVarSet ⟨n+1, by omega⟩) -- only g is now a goal
/-- The cost of a concatenation of paths is the sum of the costs. -/
private lemma PlanningTask.Path.cost_append {n : ℕ} {pt : PlanningTask n} {a b c : State n}
    (p : PlanningTask.Path pt a b) (q : PlanningTask.Path pt b c) : (p.append q).cost = p.cost + q.cost := by
  induction p <;> simp_all [ PlanningTask.Path.append ]
  · rfl
  · simp_all [ PlanningTask.Path.cost ]
    ring

/-
In a delete relaxation every action has an empty delete effect.
-/
private lemma dr_action_del_empty {n : ℕ} (X : PlanningTask n) {a : Action n}
    (ha : a ∈ (delete_relaxation X).actions) : a.del = ∅ := by
  unfold delete_relaxation at ha;
  simp_all +decide [PlanningTask.actions];
  unfold delete_relax_action at ha; aesop;

private lemma lift_forward {n : ℕ} (prob : PlanningTask n) {S1 S2 : State n}
    (p : PlanningTask.Path (delete_relaxation prob) S1 S2)
    {T0 : State (n + 2)}
    (hi : (⟨n, by omega⟩ : Fin (n + 2)) ∈ T0)
    (hsub : ∀ x ∈ S1, (Fin.castLE (show n ≤ n + 2 by omega) x) ∈ T0) :
    ∃ T2 : State (n + 2),
      (⟨n, by omega⟩ : Fin (n + 2)) ∈ T2 ∧
      (∀ x ∈ S2, (Fin.castLE (show n ≤ n + 2 by omega) x) ∈ T2) ∧
      ∃ q : PlanningTask.Path (delete_relaxation (i_g_normal_form prob)) T0 T2, q.cost = p.cost := by
  induction' p with a S_mid hS_mid succ rest ih generalizing T0;
  · exact ⟨ T0, hi, hsub, PlanningTask.Path.empty T0, rfl ⟩;
  · obtain ⟨a0, ha0⟩ : ∃ a0 : Action n, S_mid = delete_relax_action a0 ∧ a0 ∈ prob.actions := by
      unfold delete_relaxation at ih; simp_all +decide [PlanningTask.actions];
      grind;
    rename_i h₁ h₂ h₃;
    -- Let `T0' := T0 ∪ emb '' (a0.add)` be the successor of `T0` under `A` (delete-relaxed: `Successor A T0 T0'` with no deletions).
    obtain ⟨A, hA⟩ : ∃ A : Action (n + 2), A = delete_relax_action (Action.mk a0.name (VarSet.ofList ((a0.pre.toList.map (Fin.castLE (by omega))) ++ [Fin.mk n (by omega)])) (VarSet.ofList (a0.add.toList.map (Fin.castLE (by omega)))) (VarSet.ofList (a0.del.toList.map (Fin.castLE (by omega)))) a0.cost) ∧ A ∈ (delete_relaxation (i_g_normal_form prob)).actions := by
      unfold delete_relaxation i_g_normal_form; simp +decide [PlanningTask.actions] ;
      unfold PlanningTask.actions at ha0; aesop;
    have hT0' : ⟨n, by omega⟩ ∈ (T0 ∪ A.add) ∧ (∀ x ∈ succ, Fin.castLE (by omega) x ∈ (T0 ∪ A.add)) := by
      constructor
      · exact Or.inl hi
      · intro x hx
        rw [h₁.2] at hx
        rcases hx with hx | hx
        · exact Or.inl (hsub x hx.1)
        · apply Or.inr
          have hx0 : x ∈ a0.add := by
            rw [ha0.1] at hx
            simpa [delete_relax_action] using hx
          have hx' : x ∈ a0.add.toList := by simpa using hx0
          have hm : Fin.castLE (by omega) x ∈
              VarSet.ofList (a0.add.toList.map (Fin.castLE (by omega))) := by
            rw [← VarSet.mem_val]
            exact mem_val_ofList.mpr (List.mem_map.mpr ⟨x, hx', rfl⟩)
          simpa [hA.1, delete_relax_action] using hm
    obtain ⟨ T2, hT2₁, hT2₂, q, hq ⟩ := h₃ hT0'.1 hT0'.2;
    refine' ⟨ T2, hT2₁, hT2₂, PlanningTask.Path.cons A ( T0 ∪ A.add ) _ _ q, _ ⟩ <;> simp_all +decide [ PlanningTask.Path.cost ];
    · exact hA.1 ▸ hA.2;
    · constructor;
      · intro x hx; simp_all +decide [ delete_relax_action ] ;
        cases h₁ ; aesop;
      · unfold delete_relax_action; aesop;
    · unfold delete_relax_action; aesop;

/-
The single delete-relaxed "init" step of the normal form: from the initial state (only `i`)
we reach a state containing `i` and the embedding of every original initial fact, at cost 0.
-/
private lemma ignf_init_path {n : ℕ} (prob : PlanningTask n) :
    ∃ T : State (n + 2),
      (⟨n, by omega⟩ : Fin (n + 2)) ∈ T ∧
      (∀ x ∈ (delete_relaxation prob).init, (Fin.castLE (show n ≤ n + 2 by omega) x) ∈ T) ∧
      ∃ q : PlanningTask.Path (delete_relaxation (i_g_normal_form prob))
        (delete_relaxation (i_g_normal_form prob)).init T, q.cost = 0 := by
          constructor;
          swap;
          exact {x | x = ⟨n, by omega⟩ ∨ ∃ y ∈ prob.init', x = Fin.castLE (by omega) y};
          simp +decide [ mem_convertState, PlanningTask.init, delete_relaxation ];
          refine' ⟨ fun x hx => Or.inr hx, _, _ ⟩;
          refine' PlanningTask.Path.cons _ _ _ _ ( PlanningTask.Path.empty _ );
          exact Action.mk "init" ( singletonVarSet ⟨ n, by omega ⟩ ) ( VarSet.ofList ( prob.init'.toList.map ( Fin.castLE ( by omega ) ) ) ) ∅ 0;
          all_goals norm_num [ i_g_normal_form, delete_relax_action ];
          all_goals norm_num [ PlanningTask.actions,PlanningTask.actions',PlanningTask.Path.cost ];
          unfold Successor; simp +decide [ singletonVarSet, VarSet.ofList ] ;
          unfold Applicable; simp +decide [ Finset.ext_iff, Set.ext_iff ] ;
          simp +decide [ Finset.subset_iff, Set.subset_def ];
          intro x; by_cases hx : x.val < n <;> simp +decide [ hx, Fin.ext_iff ] ;
          · exact ⟨ fun h => h.imp id fun h => ⟨ ⟨ x, hx ⟩, h, rfl ⟩, fun h => h.imp id fun ⟨ a, ha, ha' ⟩ => by simpa [ ha' ] using ha ⟩;
          · grind

private lemma ignf_goal_path {n : ℕ} (prob : PlanningTask n) {T2 : State (n + 2)}
    (hgoal : ∀ x ∈ prob.goal'.toList, (Fin.castLE (show n ≤ n + 2 by omega) x) ∈ T2) :
    ∃ T3 : State (n + 2),
      (delete_relaxation (i_g_normal_form prob)).GoalState T3 ∧
      ∃ q : PlanningTask.Path (delete_relaxation (i_g_normal_form prob)) T2 T3, q.cost = 0 := by
  refine' ⟨ T2 ∪ { ⟨ n + 1, by linarith ⟩ }, _, PlanningTask.Path.cons _ _ _ _ ( PlanningTask.Path.empty _ ), _ ⟩ <;> norm_num [ delete_relaxation, i_g_normal_form, PlanningTask.actions ];
  rotate_left;
  exact delete_relax_action ⟨ "goal", VarSet.ofList ( map ( Fin.castLE ( by omega ) ) prob.goal'.toList ), singletonVarSet ⟨ n + 1, by omega ⟩, ∅, 0 ⟩;
  all_goals norm_num [ delete_relax_action, PlanningTask.Path.cost ];
  · constructor <;> simp +decide [ singletonVarSet, PlanningTask.GoalState ];
    · intro x hx; simp_all +decide [ mem_val_ofList ] ;
      grind;
    · ext; simp [VarSet.ofList];
      tauto;
  · intro x hx; simp_all +decide [ singletonVarSet ] ;

private lemma ignf_dr_plan_of_dr_plan {n : ℕ} (prob : PlanningTask n)
    (plan : PlanningTask.Plan (delete_relaxation prob) (delete_relaxation prob).init) :
    ∃ eplan : PlanningTask.Plan (delete_relaxation (i_g_normal_form prob))
        (delete_relaxation (i_g_normal_form prob)).init,
      eplan.path.cost = plan.path.cost := by
  obtain ⟨T0, hi0, hinit, q0, hq0⟩ := ignf_init_path prob
  obtain ⟨T2, _hi2, hlast, q1, hq1⟩ := lift_forward prob plan.path hi0 hinit
  obtain ⟨T3, hgoalstate, q2, hq2⟩ := ignf_goal_path prob (T2 := T2) (by
    intro x hx
    exact hlast x (plan.goal (mem_convertVarSet.mpr (VarSet.mem_toList.mp hx))))
  refine ⟨⟨T3, (q0.append q1).append q2, hgoalstate⟩, ?_⟩
  simp only [PlanningTask.Path.cost_append, hq0, hq1, hq2, Nat.add_zero, Nat.zero_add]

private lemma dr_path_mono {n : ℕ} {pt : PlanningTask n} (hdel : ∀ a ∈ pt.actions, a.del = ∅)
    {s1 s2 : State n} (p : PlanningTask.Path pt s1 s2) : s1 ⊆ s2 := by
  induction p;
  · exact Set.Subset.rfl;
  · rename_i a s1 s2 s3 ha succ π ih;
    intro x hx; have := succ.2; simp_all +decide [ Finset.subset_iff, Set.subset_def ] ;

private lemma ep_goal_facts {n : ℕ} (prob : PlanningTask n) {E1 E2 : State (n + 2)}
    (q : PlanningTask.Path (delete_relaxation (i_g_normal_form prob)) E1 E2)
    (h1 : (⟨n + 1, by omega⟩ : Fin (n + 2)) ∉ E1)
    (h2 : (⟨n + 1, by omega⟩ : Fin (n + 2)) ∈ E2) :
    ∀ x ∈ convertVarSet prob.goal', (Fin.castLE (show n ≤ n + 2 by omega) x) ∈ E2 := by
                                                  have h_goal : ∀ {s1 s2 : State (n + 2)}, (⟨n + 1, by omega⟩ : Fin (n + 2)) ∈ s2 → ∀ q : PlanningTask.Path (delete_relaxation (i_g_normal_form prob)) s1 s2, (⟨n + 1, by omega⟩ : Fin (n + 2)) ∉ s1 → ∀ x ∈ convertVarSet prob.goal', (Fin.castLE (by omega) x) ∈ s2 := by
                                                    intros s1 s2 hs2 q hs1 x hx;
                                                    induction q <;> simp_all +decide [ Fin.castLE ];
                                                    rename_i a s1 s2 s3 π ih;
                                                    unfold delete_relaxation at s3; simp_all +decide [ PlanningTask.actions ] ;
                                                    unfold i_g_normal_form at s3; simp_all +decide [ PlanningTask.actions' ] ;
                                                    rcases s3 with ⟨ a, ⟨ ⟨ b, hb, rfl ⟩ | rfl | rfl, rfl ⟩ ⟩ <;> simp_all +decide [ delete_relax_action ];
                                                    · exact ih fun y hy => ne_of_lt ( Nat.lt_succ_of_le ( Nat.le_of_lt_succ ( by simp +decide [ Fin.ext_iff ] ) ) );
                                                    · exact ih fun x hx => ne_of_lt ( Nat.lt_succ_of_le ( Nat.le_of_lt_succ ( by simp +decide [ Fin.ext_iff ] ) ) );
                                                    · cases π ; simp_all +decide [ singletonVarSet ];
                                                      rename_i h₁ h₂;
                                                      have := dr_path_mono ( show ∀ a ∈ ( delete_relaxation ( i_g_normal_form prob ) ).actions, a.del = ∅ from ?_ ) s2; simp_all +decide [ Finset.subset_iff, Set.subset_def ] ;
                                                      · exact this _ ( Or.inl ( h₁ _ hx ) );
                                                      · grind +suggestions;
                                                  exact h_goal h2 q h1

private lemma castLE_mem_map_castLE {n m : ℕ} (h : n ≤ m) (l : List (Fin n)) (x : Fin n) :
    (Fin.castLE h x) ∈ (l.map (Fin.castLE h)).toFinset ↔ x ∈ l.toFinset := by
  simp_all only [mem_toFinset, mem_map, Fin.castLE_inj, exists_eq_right]

/-
Prepending a projected original action to an original delete-relaxed path.
-/
private lemma project_cons_embedded {n : ℕ} (prob : PlanningTask n) {a : Action n}
    (ha : a ∈ prob.actions') {D0 F : State n} (hpre : (↑a.pre : Set (Fin n)) ⊆ D0)
    (dq : PlanningTask.Path (delete_relaxation prob) (D0 ∪ (↑a.add : Set (Fin n))) F) :
    ∃ dq' : PlanningTask.Path (delete_relaxation prob) D0 F, dq'.cost = dq.cost + a.cost := by
  refine' ⟨ PlanningTask.Path.cons _ _ _ _ dq, _ ⟩;
  exact delete_relax_action a;
  all_goals norm_num [ delete_relax_action, PlanningTask.Path.cost ];
  · unfold delete_relaxation; simp +decide [ PlanningTask.actions ] ;
    exact ⟨ a, ha, rfl ⟩;
  · constructor <;> aesop

private lemma project_backward {n : ℕ} (prob : PlanningTask n) {E1 E2 : State (n + 2)}
    (q : PlanningTask.Path (delete_relaxation (i_g_normal_form prob)) E1 E2)
    {D0 : State n}
    (hD : convertState prob.init' ⊆ D0)
    (hD0 : {x : Fin n | (Fin.castLE (show n ≤ n + 2 by omega) x) ∈ E1} ⊆ D0) :
    ∃ (D' : State n),
      {x : Fin n | (Fin.castLE (show n ≤ n + 2 by omega) x) ∈ E2} ⊆ D' ∧
      ∃ dq : PlanningTask.Path (delete_relaxation prob) D0 D', dq.cost ≤ q.cost := by
        revert E1 E2 q D0 hD hD0;
        -- Let's unfold the definition of `i_g_normal_form` and `delete_relaxation`.
        intro E1 E2 q D0 hD hD0
        induction' q with a s1 s2 s3 ha succ π ih generalizing D0;
        · exact ⟨ _, hD0, PlanningTask.Path.empty _, rfl.le ⟩;
        · -- The action `s1` is one of three shapes: free "goal", free "init", or `delete_relax_action (embedded a0)`.
          unfold delete_relaxation i_g_normal_form at succ; simp [PlanningTask.actions] at succ; rcases succ with (rfl | rfl | ⟨ a0, ha0, rfl ⟩) <;> simp [delete_relax_action] at *;
          · rename_i h;
            unfold delete_relax_action at π; simp_all +decide [ delete_relaxation, i_g_normal_form ] ;
            obtain ⟨ D', hD', dq, hdq ⟩ := h hD ( by
              exact fun x hx => hx.elim ( fun hx => hD0 hx ) fun hx => hD ( by simpa [ convertState ] using hx ) );
            exact ⟨ D', hD', dq, by simpa [ PlanningTask.Path.cost ] using hdq ⟩;
          · cases π ; simp_all +decide [ Successor ];
            rename_i h₁ h₂ h₃; specialize h₃ hD; simp_all +decide [ delete_relax_action ] ;
            contrapose! h₃; simp_all +decide [ Set.subset_def ] ;
            constructor;
            · rintro x ( hx | hx ) <;> [ exact hD0 x hx; exact absurd hx ( by exact ne_of_lt ( Nat.lt_succ_of_le ( Nat.le_of_lt_succ ( by simp +decide [ Fin.ext_iff ] ) ) ) ) ];
            · intro D' hD' dq; specialize h₃ D' hD' dq; simp_all +decide [ PlanningTask.Path.cost ] ;
          · obtain ⟨ D', hD', dq, hdq ⟩ := ‹∀ { D0 : State n }, convertState prob.init' ⊆ D0 → { x | Fin.castLE _ x ∈ s3 } ⊆ D0 → ∃ D', { x | Fin.castLE _ x ∈ ha } ⊆ D' ∧ ∃ dq : PlanningTask.Path ( delete_relaxation prob ) D0 D', dq.cost ≤ ih.cost› ( show convertState prob.init' ⊆ D0 ∪ a0.add from by
                                                                                                                                                                                                                                                        exact Set.Subset.trans hD ( Set.subset_union_left ) ) ( show { x | Fin.castLE _ x ∈ s3 } ⊆ D0 ∪ a0.add from by
                                                                                                                                                                                                                                                                                                                              intro x hx; cases' π with h1 h2 h3; simp_all +decide [ Finset.subset_iff, Set.subset_def ] ;
                                                                                                                                                                                                                                                                                                                              cases hx <;> simp_all +decide [ delete_relax_action ] );
            obtain ⟨ dq', hdq' ⟩ := project_cons_embedded prob ha0 ( show ( a0.pre : Set ( Fin n ) ) ⊆ D0 from by
                                                                      intro x hx; have := π.1; simp_all +decide [ Finset.subset_iff, Set.subset_def ] ;
                                                                      exact hD0 x ( by have := π.1; exact this ( by unfold delete_relax_action; simp +decide [ mem_val_ofList ] ; aesop ) ) ) dq;
            exact ⟨ D', hD', dq', by simp +decide [ PlanningTask.Path.cost, hdq', hdq ] ⟩

private lemma dr_plan_of_ignf_dr_plan {n : ℕ} (prob : PlanningTask n)
    (eplan : PlanningTask.Plan (delete_relaxation (i_g_normal_form prob))
        (delete_relaxation (i_g_normal_form prob)).init) :
    ∃ plan : PlanningTask.Plan (delete_relaxation prob) (delete_relaxation prob).init,
      plan.path.cost ≤ eplan.path.cost := by
        obtain ⟨eplan, hplan⟩ := eplan;
        rename_i hgoal;
        obtain ⟨ D', hD', dq, hdq ⟩ := project_backward prob hplan ( show convertState prob.init' ⊆ convertState prob.init' from Set.Subset.refl _ ) ( by
                                                                      unfold delete_relaxation i_g_normal_form; simp +decide [ PlanningTask.init ] ;
                                                                      grind );
        refine' ⟨ ⟨ D', dq, _ ⟩, hdq ⟩;
        intro x hx; have := hgoal; simp_all +decide [ PlanningTask.GoalState ] ;
        have := ep_goal_facts prob hplan ( show ( ⟨ n + 1, by omega ⟩ : Fin ( n + 2 ) ) ∉ ( delete_relaxation ( i_g_normal_form prob ) ).init from ?_ ) ( show ( ⟨ n + 1, by omega ⟩ : Fin ( n + 2 ) ) ∈ eplan from ?_ );
        · exact hD' ( this x ( by simpa [ convertVarSet ] using hx ) );
        · unfold delete_relaxation i_g_normal_form; simp +decide [ PlanningTask.init ] ;
        · exact hgoal ( by simp +decide [ convertVarSet, delete_relaxation, i_g_normal_form ] )

lemma i_g_normal_form_keeps_h_plus {n : ℕ} {prob : PlanningTask n}
    (hsolv : ¬ PlanningTask.Unsolvable (delete_relaxation prob)) :
   h_plus prob prob.init' = h_plus (i_g_normal_form prob) (i_g_normal_form prob).init'  := by
     -- Since `planner A (fun _=>0) ≠ none`, it must be `some retA`.
     obtain ⟨retA, hA⟩ : ∃ retA, planner (delete_relaxation prob) (fun _ => 0) = some retA := by
       contrapose! hsolv; have := planner_complete ( delete_relaxation prob ) ( fun _ => 0 ) ( zero_heur_admissible' ( delete_relaxation prob ) ) ; aesop;
     obtain ⟨retB, hB⟩ : ∃ retB, planner (delete_relaxation (i_g_normal_form prob)) (fun _ => 0) = some retB := by
       have hB : ¬PlanningTask.Unsolvable (delete_relaxation (i_g_normal_form prob)) := by
         exact fun h => hsolv <| by obtain ⟨ eplan, heplan ⟩ := ignf_dr_plan_of_dr_plan prob retA; exact h.elim eplan;
       exact Option.ne_none_iff_exists'.mp ( planner_complete _ _ ( zero_heur_admissible' _ ) |> fun h => by tauto );
     -- By `planner_optimal`, we have `retA.path.cost ≤ retB.path.cost`.
     have h_le : retA.path.cost ≤ retB.path.cost := by
       obtain ⟨plan, hplan⟩ := dr_plan_of_ignf_dr_plan prob retB;
       convert planner_optimal ( delete_relaxation prob ) ( fun _ => 0 ) ( zero_heur_admissible _ ) ( show ( planner ( delete_relaxation prob ) fun _ => 0 ).isSome from by simp +decide [ hA ] ) plan |> le_trans <| hplan using 1;
       grind +splitIndPred;
     -- By `planner_optimal`, we have `retB.path.cost ≤ retA.path.cost`.
     have h_ge : retB.path.cost ≤ retA.path.cost := by
       have := ignf_dr_plan_of_dr_plan prob retA;
       have := planner_optimal ( delete_relaxation ( i_g_normal_form prob ) ) ( fun _ => 0 ) ( zero_heur_admissible _ ) ( show ( planner ( delete_relaxation ( i_g_normal_form prob ) ) ( fun _ => 0 ) ).isSome from by simp +decide [ hB ] ) this.choose;
       grind;
     unfold h_plus; simp_all +decide [ delete_relaxation, i_g_normal_form ] ;
     exact le_antisymm h_le h_ge

lemma i_g_normal_form_keeps_solvability {n : ℕ} {prob : PlanningTask n} :
    PlanningTask.Unsolvable (delete_relaxation prob) ↔
      PlanningTask.Unsolvable (delete_relaxation ((i_g_normal_form prob))) := by
  constructor <;> intro h
  · -- A delete-relaxed plan of the normal form would project back to one of the original task.
    exact ⟨fun eplan => h.false (dr_plan_of_ignf_dr_plan prob eplan).choose⟩
  · -- A delete-relaxed plan of the original task lifts to one of the normal form.
    exact ⟨fun plan => h.false (ignf_dr_plan_of_dr_plan prob plan).choose⟩


/- Theory of PCFs and justification graphs -/

/-- should be a type of functions that take an action from prob and return one of their preconditions -/
abbrev precondition_choice_function {n : ℕ} (prob : PlanningTask n):=
    Π (a : {b : Action n // b ∈ prob.actions'}), { p : Fin n // p ∈ a.val.pre}

/-- A planning problem `prob` *has preconditions* if every one of its actions has at least one
precondition fact.  This is exactly the condition under which a `precondition_choice_function prob`
can exist (the subtype `{ p : Fin n // p ∈ a.val.pre }` is nonempty for every action).  The i/g
normal form of a problem with a nonempty goal always has this property, and cost partitioning
preserves it. -/
def has_preconditions {n : ℕ} (prob : PlanningTask n) : Prop :=
  ∀ a ∈ prob.actions', a.pre.toList ≠ []

/-
An element of `a.val.pre.toList` is a member of `a.val.pre` (the `Set`-level precondition).
-/
lemma mem_pre_of_mem_pre_val {n : ℕ} (a : Action n) {x : Fin n} (hx : x ∈ a.pre.toList) :
    x ∈ a.pre := by
  contrapose! hx;
  exact fun h => hx <| by simpa [ Set.ext_iff ] using h;

lemma partition_STRIPS_has_preconditions {n P : ℕ} (prob : PlanningTask n)
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
lemma i_g_normal_form_has_preconditions {n : ℕ} (prob : PlanningTask n)
    (hg : prob.goal'.toList ≠ []) :
    has_preconditions (i_g_normal_form prob) := by
      intro a ha;
      unfold i_g_normal_form at ha;
      unfold VarSet.ofList at *; simp_all +decide [ List.map ] ;
      rcases ha with ( ⟨ a, ha, rfl ⟩ | rfl | rfl ) <;> simp_all +decide [ singletonVarSet ];
      · simp +decide [ VarSet.toList ];
        exact ne_of_apply_ne List.length ( by simp +decide [ Finset.length_sort ] );
      · unfold VarSet.ofList; simp +decide [ List.SortedLT ] ;
        exact List.ne_nil_of_mem ( List.mem_singleton_self _ );
      · simp_all +decide [ List.eq_nil_iff_forall_not_mem ]

def relax_invariant_pcf {n : ℕ} (prob : PlanningTask n) (pcf : precondition_choice_function prob) : Prop :=
  ∀ (a b : {x : Action n // x ∈ prob.actions'}),
    delete_relax_action a.val = delete_relax_action b.val → (↑(pcf a) : Fin n) = (↑(pcf b) : Fin n)



/-- the IG normalform has only one init fact and one goal fact and we are able to obtain them -/

def unitary_init {n : ℕ} (prob : PlanningTask n) : Prop := prob.init.ncard == 1
def unitary_goal {n : ℕ} (prob : PlanningTask n) : Prop := prob.goal'.toList.length == 1

/-
In the i/g normal form the only initial fact is the auxiliary variable `i` (at index `n`).
-/
lemma i_g_normalform_init_eq {n : ℕ} (prob : PlanningTask n) :
    (i_g_normal_form prob).init = {(⟨n, by omega⟩ : Fin (n + 2))} := by
      convert Set.ext _;
      simp +decide [ i_g_normal_form, PlanningTask.init' ];
      simp +decide [ PlanningTask.init, SetLike.coe ];
      exact fun x => ⟨ fun hx => Fin.ext hx, fun hx => hx ▸ rfl ⟩

lemma i_g_normalform_is_unitary_init {n : ℕ} (prob : PlanningTask n):
    unitary_init (i_g_normal_form prob) := by
  rw [unitary_init, beq_iff_eq, i_g_normalform_init_eq, Set.ncard_singleton]

lemma i_g_normalform_is_unitary_goal {n : ℕ} (prob : PlanningTask n):
    unitary_goal (i_g_normal_form prob) := by
      rw [ i_g_normal_form ];
      use Eq.symm (by
      rw [ eq_comm, ← Multiset.coe_card ] ;
      rw [ ← Multiset.toFinset_card_of_nodup ] <;> norm_num [ singletonVarSet ];
      · rw [ Finset.card_eq_one ] ; use ⟨ n + 1, by omega ⟩ ; ext ; simp +decide [ mem_val_ofList ] ;
      · grind +suggestions)

lemma init_eq_varset_toFinset {n : ℕ} (prob : PlanningTask n) :
    prob.init = ↑(prob.init').toList.toFinset :=
  (BitVec.coe_toList_toFinset prob.init').symm
lemma init_ncard_eq_varset_length {n : ℕ} (prob : PlanningTask n) :
    prob.init.ncard = (prob.init').toList.length :=
  BitVec.ncard_convertState_eq_toList_length prob.init'
lemma unitary_init_varset_length {n : ℕ} (prob : PlanningTask n) (u : unitary_init prob) :
    (prob.init').toList.length = 1 := by
  have h : prob.init.ncard = 1 := by simpa [unitary_init, beq_iff_eq] using u
  rw [← init_ncard_eq_varset_length]; exact h
def get_unitary_init {n : ℕ} (prob : PlanningTask n) (u : unitary_init prob) : Fin n :=
  prob.init'.toList.head
    (List.ne_nil_of_length_pos (by rw [unitary_init_varset_length prob u]; norm_num))
def get_unitary_goal{n : ℕ} (prob : PlanningTask n) (u : unitary_goal prob) : Fin n :=
  prob.goal'.toList.head (by unfold unitary_goal at u ; grind)

lemma get_unitary_init_is_init {n : ℕ} (prob : PlanningTask n) (u : unitary_init prob):
    prob.init = {get_unitary_init prob u} := by
  have hlen := unitary_init_varset_length prob u
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hlen
  have hhead : get_unitary_init prob u = a := by simp [get_unitary_init, ha]
  rw [init_eq_varset_toFinset, hhead, ha]
  simp
lemma get_unitary_goal_is_goal {n : ℕ} (prob : PlanningTask n) (u : unitary_goal prob):
    prob.goal'.toList = [get_unitary_goal prob u] := by
  have hlen : prob.goal'.toList.length = 1 := by
    have := u; simp only [unitary_goal, beq_iff_eq] at this; exact this
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hlen
  simp [get_unitary_goal, ha]



/-- the justification graph selects one precondition per action and connects facts using them - and ignoring their deleting effects. We use NatGraph here, as we have search algorithms for them -/
def justification_graph {n : ℕ} (prob : PlanningTask n) (pcf : precondition_choice_function prob) : NatGraph (Fin n) :=
  -- We quantify over the subtype `{b // b ∈ prob.actions'}` so that the precondition choice
  -- function `pcf` can be applied directly (it needs the membership witness).  Membership is
  -- phrased through `a.val.add.toList.toFinset`, which is definitionally `t ∈ a.val.add`, so that
  -- the relation is decidable.
  let edges : Fin n → Fin n → Prop := fun f t =>
    ∃ a : {b : Action n // b ∈ prob.actions'}, f = (↑(pcf a) : Fin n) ∧ t ∈ a.val.add.toList.toFinset

  let dg : Digraph (Fin n) := Digraph.mk edges
  let dg_dec : DecidableRel dg.Adj := fun f t => inferInstanceAs (Decidable (edges f t))

  -- cost of an edge is the cheapest cost of an action that created that edge.  We filter the
  -- *attached* action list so that `pcf a` (which needs the membership witness) and `a.val.add`
  -- are well typed, and we collect the underlying actions afterwards.
  let cost : (u v : Fin n) → dg.Adj u v → ℕ := fun f t adj =>
    let edgeActions : List (Action n) := (prob.actions'.attach.filter (fun a =>
      decide (f = (↑(pcf a) : Fin n) ∧ t ∈ a.val.add.toList.toFinset))).map (·.val)
    (edgeActions.map (·.cost)).min (by
      obtain ⟨a, hf, ht⟩ := adj
      have ha : a.val ∈ edgeActions := by
        simp only [edgeActions, List.mem_map, List.mem_filter]
        exact ⟨a, ⟨List.mem_attach _ _, by simp only [decide_eq_true_eq]; exact ⟨hf, ht⟩⟩, rfl⟩
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


def landmark_induced_by_cut {n : ℕ} (prob : PlanningTask n) (cut : List (Fin n × Fin n)) (pcf : precondition_choice_function prob) : List (Action n) :=
    cut.flatMap (fun (f,t) => (prob.actions'.attach.filter (fun a =>
      decide (f = (↑(pcf a) : Fin n) ∧ t ∈ a.val.add.toList.toFinset)
    )).map (·.val) )

/-
Core reachability lemma for the cut argument.  Replaying a delete-relaxed path of `prob`,
every fact that is true at the end of the path can be reached, in the *cut* justification graph
`remove_edges (justification_graph prob pcf) cut`, from any source `src` that already reaches the
start facts — **provided** none of the path's actions witnesses a cut edge (`Hwit`).

The induction tracks `Hsrc`, the set of currently reachable facts: a delete-relaxed action `a`
with chosen precondition `pcf a` (true, hence already reachable) adds facts `y ∈ a.add`; the
justification edge `pcf a → y` survives the cut by `Hwit`, extending the reachability.
-/
private lemma jgraph_reach_of_dr_path {n : ℕ} (prob : PlanningTask n)
    (pcf : precondition_choice_function prob) (cut : List (Fin n × Fin n))
    (src : Fin n) :
    ∀ {S T : State n} (p : PlanningTask.Path (delete_relaxation prob) S T),
    (∀ (a0 : {b : Action n // b ∈ prob.actions'}),
      delete_relax_action a0.val ∈ p.actionsUsed →
      ∀ y ∈ a0.val.add.toList.toFinset, ((↑(pcf a0) : Fin n), y) ∉ cut) →
    (∀ s ∈ S, Nonempty ((remove_edges (justification_graph prob pcf) cut).Walk src s)) →
    ∀ t ∈ T, Nonempty ((remove_edges (justification_graph prob pcf) cut).Walk src t) := by
      intros S T p hp hsrc t ht;
      induction' p with a s1 s2 s3 ha succ ih generalizing src;
      · exact hsrc t ht;
      · rename_i h₁ h₂;
        apply h₂ src (fun a0 ha0 => hp a0 (by
        exact List.mem_cons_of_mem _ ha0)) (fun s hs => by
          cases ih ; simp_all +decide [ PlanningTask.Path.actionsUsed ];
          cases hs <;> simp_all +decide [ Applicable ];
          unfold delete_relaxation at succ; simp_all +decide [ PlanningTask.actions ] ;
          obtain ⟨ a, ha, rfl ⟩ := succ; specialize hp a ha; simp_all +decide [ delete_relax_action ] ;
          obtain ⟨ p, hp ⟩ := hsrc ( pcf ⟨ a, ha ⟩ ) ( by
            exact ‹ ( a.pre : Set ( Fin n ) ) ⊆ s2 › ( by simp [ Set.ext_iff ] ) );
          · exact ⟨ WeightedDiGraph.Walk.cons ( by
              unfold remove_edges; simp +decide [ justification_graph ] ;
              exact ⟨ ⟨ a, ⟨ ha, rfl ⟩, by assumption ⟩, hp s ‹_› ⟩ ) ( WeightedDiGraph.Walk.nil ) ⟩;
          · exact ⟨ WeightedDiGraph.Walk.cons ‹_› ( ‹WeightedDiGraph.Walk _ _›.append ( WeightedDiGraph.Walk.cons ( by
              exact ⟨ ⟨ ⟨ a, ha ⟩, rfl, by aesop ⟩, by aesop ⟩ ) WeightedDiGraph.Walk.nil ) ) ⟩) ht

private lemma mem_landmark_induced {n : ℕ} (prob : PlanningTask n) (cut : List (Fin n × Fin n))
    (pcf : precondition_choice_function prob)
    (a0 : {b : Action n // b ∈ prob.actions'}) (f t : Fin n)
    (hft : (f, t) ∈ cut) (hf : f = (↑(pcf a0) : Fin n)) (ht : t ∈ a0.val.add.toList.toFinset) :
    a0.val ∈ landmark_induced_by_cut prob cut pcf := by
      simp_all +decide [ landmark_induced_by_cut ];
      exact ⟨ t, hft, a0.2, ht ⟩

private lemma landmark_subset_actions {n : ℕ} (prob : PlanningTask n) (cut : List (Fin n × Fin n))
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
lemma landmark_induced_closed_under_relax {n : ℕ} (prob : PlanningTask n) (cut : List (Fin n × Fin n))
    (pcf : precondition_choice_function prob) (hinv : relax_invariant_pcf prob pcf)
    {a b : Action n} (ha : a ∈ landmark_induced_by_cut prob cut pcf)
    (hb : b ∈ prob.actions') (hrel : delete_relax_action b = delete_relax_action a) :
    b ∈ landmark_induced_by_cut prob cut pcf := by
  unfold landmark_induced_by_cut at *;
  simp +zetaDelta at *;
  obtain ⟨ c, hc₁, hc₂ ⟩ := ha;
  use c;
  obtain ⟨ ha₁, ha₂ ⟩ := hc₁;
  have := hinv ⟨ a, ha₁ ⟩ ⟨ b, hb ⟩ ; simp_all +decide [ delete_relax_action ] ;

lemma cuts_in_justification_graph_are_delete_relaxed_landmarks {n : ℕ} (prob : PlanningTask n)
    (u_i : unitary_init prob)
    (u_g : unitary_goal prob)
    (pcf : precondition_choice_function prob) (cut : List ((Fin n) × (Fin n))):
    cut_in_graph (justification_graph prob pcf) (get_unitary_init prob u_i) (get_unitary_goal prob u_g) cut →
      is_delete_relaxed_disjunctive_action_landmark_for_state prob (landmark_induced_by_cut prob cut pcf) prob.init' := by
        intro hcut
        constructor;
        · simp +decide [ PlanningTask.actions, delete_relaxation ];
          exact fun x hx => ⟨ x, landmark_subset_actions prob cut pcf x hx, rfl ⟩;
        · contrapose! hcut
          generalize_proofs at *;
          obtain ⟨plan, hplan⟩ := hcut
          have h_reachable : ∀ t ∈ plan.last, Nonempty ((remove_edges (justification_graph prob pcf) cut).Walk (get_unitary_init prob u_i) t) := by
            apply jgraph_reach_of_dr_path prob pcf cut (get_unitary_init prob u_i) plan.path
            generalize_proofs at *;
            · intro a0 ha0 y hy hcut
              have h_mem : a0.val ∈ landmark_induced_by_cut prob cut pcf := by
                exact mem_landmark_induced prob cut pcf a0 _ _ hcut rfl hy
              generalize_proofs at *;
              exact hplan a0.val h_mem ha0;
            · have h_reachable : convertState prob.init' = {get_unitary_init prob u_i} := by
                convert get_unitary_init_is_init prob u_i using 1
              generalize_proofs at *;
              simp [h_reachable];
              exact ⟨ WeightedDiGraph.Walk.nil ⟩
          generalize_proofs at *;
          have h_goal_reachable : Nonempty ((remove_edges (justification_graph prob pcf) cut).Walk (get_unitary_init prob u_i) (get_unitary_goal prob u_g)) := by
            have h_goal_reachable : get_unitary_goal prob u_g ∈ prob.goal'.toList.toFinset := by
              have := get_unitary_goal_is_goal prob u_g; aesop;
            generalize_proofs at *;
            exact h_reachable _ ( plan.goal <| by simpa [PlanningTask.goal'] using h_goal_reachable)
          generalize_proofs at *;
          exact ⟨ h_goal_reachable.some.bypass, h_goal_reachable.some.bypass_isPath ⟩

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

/-
The constant-zero heuristic is admissible (costs are natural numbers, so `0` underestimates).
-/
lemma zero_heur_graph_admissible {V : Type} [FinEnum V] (g : NatGraph V) (goal : V) :
    g.admissible (fun _ => 0) goal := by
      intro v p; exact zero_le _;

lemma zero_cost_reachable_of_walk {V : Type} [FinEnum V] (g : NatGraph V) {v goal : V}
    (w : g.Walk v goal) (hw : w.cost = 0) : zero_cost_reachable g v goal := by
      have h_path : ∃ p : g.Path v goal, p.cost = 0 := by
        exact ⟨ ⟨ w.bypass, WeightedDiGraph.Walk.bypass_isPath w ⟩, by simpa using Nat.le_antisymm ( Nat.le_trans ( by exact ( WeightedDiGraph.Walk.cost_bypass_le w ) ) hw.le ) ( Nat.zero_le _ ) ⟩
      obtain ⟨p, hp⟩ : ∃ p : g.Path v goal, p.cost = 0 := h_path
      have h_complete : (NatGraph.astar (g:=g) (fun _ => 0) v goal).isSome := by
        apply NatGraph.astar_is_complete
        exact ⟨ p, fun u _ => by simp [NatGraph.hsearch_expandable] ⟩
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

/-- The source of any edge recorded in `edges_entering_goal_zone` lies outside the goal zone. -/
lemma edges_entering_goal_zone_source_not_mem {V : Type} [FinEnum V] (g : NatGraph V) (goal : V)
    {u v : V} (h : (u, v) ∈ edges_entering_goal_zone g goal) : u ∉ goal_zone g goal := by
  obtain ⟨u2, v2, hx, hu2, -, -⟩ :
      ∃ u2 v2, (u, v) = (u2, v2) ∧ u2 ∉ goal_zone g goal ∧ v2 ∈ goal_zone g goal ∧ g.Adj u2 v2 := by
    unfold edges_entering_goal_zone at h
    simp_all [List.mem_flatMap, List.mem_filterMap]
  rw [Prod.mk.injEq] at hx
  rw [hx.1]; exact hu2

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

lemma goal_zone_landmark_of_justification_graph {n : ℕ} (prob : PlanningTask n)
    (u_i : unitary_init prob) (u_g : unitary_goal prob)
    (pcf : precondition_choice_function prob):
      is_delete_relaxed_disjunctive_action_landmark_for_state prob (landmark_induced_by_cut prob (edges_entering_goal_zone (justification_graph prob pcf) (get_unitary_goal prob u_g)) pcf) prob.init'

With the new (minimum-action) edge costs this is **false**: if the unitary init fact is
zero-cost reachable to the unitary goal in the justification graph, then `init` lies in the goal
zone, no edge enters the goal zone from `init`'s side, the induced landmark can be empty, yet a
(zero cost) delete-relaxed plan exists — so the landmark property fails.  The faithful statement
adds the hypothesis `¬ zero_cost_reachable …`, exactly the situation in which the edges entering
the goal zone form a genuine init/goal cut. -/
lemma goal_zone_landmark_of_justification_graph {n : ℕ} (prob : PlanningTask n)
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
lemma justification_graph_payload_le_cost {n : ℕ} (prob : PlanningTask n)
    (pcf : precondition_choice_function prob) {f t : Fin n}
    (adj : (justification_graph prob pcf).Adj f t)
    (a0 : {b : Action n // b ∈ prob.actions'}) (hf : f = (↑(pcf a0) : Fin n))
    (ht : t ∈ a0.val.add.toList.toFinset) :
    (justification_graph prob pcf).Payload f t adj ≤ a0.val.cost := by
      have h_mem : a0.val ∈ (prob.actions'.attach.filter (fun a => decide (f = (↑(pcf a) : Fin n) ∧ t ∈ a.val.add.toList.toFinset))).map (·.val) := by
        grind +splitImp;
      obtain ⟨l, hl⟩ : ∃ l : List (Action n), l = (prob.actions'.attach.filter (fun a => decide (f = (↑(pcf a) : Fin n) ∧ t ∈ a.val.add.toList.toFinset))).map (·.val) ∧ a0.val ∈ l := by
        exact ⟨ _, rfl, h_mem ⟩;
      obtain ⟨l', hl'⟩ : ∃ l' : List ℕ, l' = l.map (·.cost) ∧ (a0.val.cost : ℕ) ∈ l' := by
        grind;
      convert List.min_le_of_mem hl'.2 using 1;
      unfold justification_graph; aesop;

lemma cost_goal_zone_landmark_of_justification_graph {n : ℕ} (prob : PlanningTask n)
    (u_i : unitary_init prob)
    (u_g : unitary_goal prob)
    (pcf : precondition_choice_function prob):
    ¬ zero_cost_reachable (justification_graph prob pcf) (get_unitary_init prob u_i) (get_unitary_goal prob u_g) →
    ∀ a ∈ (landmark_induced_by_cut prob (edges_entering_goal_zone (justification_graph prob pcf) (get_unitary_goal prob u_g)) pcf), a.cost > 0 := by
      intro h a ha
      obtain ⟨ft, hmem, ha⟩ : ∃ ft, ft ∈ edges_entering_goal_zone (justification_graph prob pcf) (get_unitary_goal prob u_g) ∧ a ∈ (prob.actions'.attach.filter (fun a => decide (ft.1 = (↑(pcf a) : Fin n) ∧ ft.2 ∈ a.val.add.toList.toFinset))).map (·.val) := by
        exact exists_of_mem_flatMap ha
      rw [ List.mem_map ] at ha
      obtain ⟨a0, ha0, rfl⟩ := ha
      rw [ List.mem_filter ] at ha0
      have hf : ft.1 = (↑(pcf a0) : Fin n) := by
        grind +splitIndPred
      have ht : ft.2 ∈ a0.val.add.toList.toFinset := by
        grind
      have hpay : (justification_graph prob pcf).Payload ft.1 ft.2 (edges_entering_goal_zone_are_edges (justification_graph prob pcf) (get_unitary_goal prob u_g) ft hmem) ≠ 0 := by
        exact edges_entering_goal_zone_dont_contain_zero_cost ( justification_graph prob pcf ) ( get_unitary_goal prob u_g ) ft hmem
      have hle : (justification_graph prob pcf).Payload ft.1 ft.2 (edges_entering_goal_zone_are_edges (justification_graph prob pcf) (get_unitary_goal prob u_g) ft hmem) ≤ a0.val.cost := by
        convert justification_graph_payload_le_cost prob pcf _ a0 hf ht using 1
      grind

/-- runs one step of landmark cutting: compute justification graph, extract cut, generate landmark and partition the cost -/
def lmcut_step {n : ℕ} (prob : PlanningTask n)
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

theorem lmcut_step_yields_landmark {n : ℕ} (prob : PlanningTask n)
    (u_i : unitary_init prob) (u_g : unitary_goal prob)
    (pcf : precondition_choice_function prob):
    is_delete_relaxed_disjunctive_action_landmark_for_state prob (lmcut_step prob u_g pcf).1 prob.init'

Since `(lmcut_step prob u_g pcf).1` is exactly the landmark induced by the edges entering the goal
zone, this is **false** without a reachability assumption, for the same reason as
`goal_zone_landmark_of_justification_graph` (a zero-cost path from init to goal yields an empty
landmark together with an existing delete-relaxed plan).  The faithful statement adds
`¬ zero_cost_reachable …`. -/
theorem lmcut_step_yields_landmark {n : ℕ} (prob : PlanningTask n)
    (u_i : unitary_init prob)
    (u_g : unitary_goal prob)
    (pcf : precondition_choice_function prob)
    (i_g_not_zero_reachable : ¬ zero_cost_reachable (justification_graph prob pcf)
      (get_unitary_init prob u_i) (get_unitary_goal prob u_g)) :
    is_delete_relaxed_disjunctive_action_landmark_for_state prob (lmcut_step prob u_g pcf).1 prob.init' :=
  goal_zone_landmark_of_justification_graph prob u_i u_g pcf i_g_not_zero_reachable

/-
Every action of the relax-equivalence closure of the cut landmark costs at least `minCost`
(the minimum cost of a landmark action), because it is delete-relaxation equivalent to some
landmark action, which shares its cost.
-/
lemma lmcut_minCost_le_cost {n : ℕ} (prob : PlanningTask n) (u_g : unitary_goal prob)
    (pcf : precondition_choice_function prob) {a : Action n}
    (ha : a ∈ get_all_equiv_delete_relaxed_actions prob (lmcut_step prob u_g pcf).1) :
    (lmcut_step prob u_g pcf).2.1 ≤ a.cost := by
  obtain ⟨l, hl, h_eq⟩ : ∃ l ∈ (lmcut_step prob u_g pcf).1, delete_relax_action a = delete_relax_action l := by
    contrapose! ha; simp_all +decide [ get_all_equiv_delete_relaxed_actions ] ;
  unfold lmcut_step at *;
  simp +zetaDelta at *;
  split_ifs <;> simp_all +decide [ delete_relax_action ];
  exact List.min_le_of_mem ( List.mem_map.mpr ⟨ l, hl, rfl ⟩ )

theorem lmcut_step_yields_partitioning {n : ℕ} (prob : PlanningTask n)
    (u_g : unitary_goal prob)
    (pcf : precondition_choice_function prob):
    is_valid_cost_partitioning prob 2 (lmcut_step prob u_g pcf).2.2 := by
  intro a;
  by_cases ha : prob.actions'[a] ∈ get_all_equiv_delete_relaxed_actions prob (lmcut_step prob u_g pcf).1;
  · have := lmcut_minCost_le_cost prob u_g pcf ha;
    unfold lmcut_step at *;
    simp +decide [ List.finRange, List.map ];
    grind +extAll;
  · unfold lmcut_step;
    simp +decide [ List.finRange ];
    split_ifs <;> norm_num;
    contradiction

lemma minCost_le_cut_edge_payload {n : ℕ} (prob : PlanningTask n)
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
      have h_edgeActions_subset_lm : (prob.actions'.attach.filter (fun a => decide (u = (↑(pcf a) : Fin n) ∧ v ∈ a.val.add.toList.toFinset))).map (·.val) ⊆ (landmark_induced_by_cut prob (edges_entering_goal_zone (justification_graph prob pcf) (get_unitary_goal prob u_g)) pcf) := by
        unfold landmark_induced_by_cut; simp [ List.subset_def ]
        grind
      have h_payload_in_lm : (justification_graph prob pcf).Payload u v adj ∈ (prob.actions'.attach.filter (fun a => decide (u = (↑(pcf a) : Fin n) ∧ v ∈ a.val.add.toList.toFinset))).map (fun a => a.val.cost) := by
        have h_payload_in_lm : (justification_graph prob pcf).Payload u v adj = (List.map (fun a => a.val.cost) (prob.actions'.attach.filter (fun a => decide (u = (↑(pcf a) : Fin n) ∧ v ∈ a.val.add.toList.toFinset)))).min (by
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

theorem lmcut_step_yields_landmark_with_heuristic_in_partition {n : ℕ} (prob : PlanningTask n)
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
lemma lmcut_closure_is_genuine {n : ℕ} (prob : PlanningTask n)
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
    simpa [PlanningTask.actions] using landmark_subset_actions prob _ pcf a ha

/-
Transfer a plan of a cost-partitioned problem to a plan of the original problem, recording for
each action used in the recovered plan its index in `prob.actions'` and the matching (cost-adapted)
action in the partitioned plan.  This works because `partition_STRIPS` only relabels costs, leaving
applicability and successor states unchanged.
-/
lemma path_partition_to_orig {n P : ℕ} (prob : PlanningTask n) (partitioning : cost_partitioning prob P)
    (p : Fin P) {s1 s2 : State n} (path' : PlanningTask.Path (partition_STRIPS prob partitioning p) s1 s2) :
    ∃ path : PlanningTask.Path prob s1 s2,
      ∀ a0 ∈ path.actionsUsed, ∃ (i : Fin prob.actions'.length),
        prob.actions'[i] = a0 ∧
        Action.mk a0.name a0.pre a0.add a0.del (partitioning p i) ∈ path'.actionsUsed := by
          by_contra! h;
          -- By definition of ` adapting the plan from the partitioned problem to the original problem, we need to show that the adapted plan is indeed a plan for the original problem. We will do this by induction on the length of the path.
          induction' path' with path'_rest a' ha' succ' ih;
          · exact absurd ( h ( PlanningTask.Path.empty _ ) ) ( by simp +decide [ PlanningTask.Path.actionsUsed ] );
          · rename_i h₁ h₂ h₃ h₄;
            obtain ⟨a0, ha0⟩ : ∃ a0 : Action n, ∃ i : Fin prob.actions'.length, prob.actions'[i] = a0 ∧ a' = ⟨a0.name, a0.pre, a0.add, a0.del, partitioning p i⟩ := by
              simp_all +decide [ PlanningTask.actions, partition_STRIPS ];
              obtain ⟨ i, hi ⟩ := List.mem_iff_getElem.mp h₁;
              obtain ⟨ hi₁, hi₂ ⟩ := hi;
              have h_mem : a' ∈ (prob.actions'.mapFinIdx (fun i a i_lt => Action.mk a.name a.pre a.add a.del (partitioning p ⟨i, i_lt⟩))) := by
                exact hi₂ ▸ List.mem_dedup.mp ( List.getElem_mem _ ) |> fun h => by simpa [ partition_STRIPS ] using h;
              obtain ⟨ i, hi ⟩ := List.mem_mapFinIdx.mp h_mem;
              exact ⟨ ⟨ i, hi.choose ⟩, hi.choose_spec.symm ⟩;
            obtain ⟨path_rest, hpath_rest⟩ : ∃ path_rest : PlanningTask.Path prob succ' ih, ∀ a0 ∈ path_rest.actionsUsed, ∃ i : Fin prob.actions'.length, prob.actions'[i] = a0 ∧ Action.mk a0.name a0.pre a0.add a0.del (partitioning p i) ∈ h₃.actionsUsed := by
              exact not_forall_not.mp fun h => h₄ <| by simpa using h;
            generalize_proofs at *;
            specialize h ( PlanningTask.Path.cons a0 succ' ( by
              unfold PlanningTask.actions; aesop; ) ( by
              unfold Successor at *; aesop; ) path_rest )
            generalize_proofs at *;
            simp_all +decide [ PlanningTask.Path.actionsUsed ];
            grind

/-
A genuine disjunctive action landmark of `prob` transfers, via cost adaptation, to a genuine
disjunctive action landmark of any cost-partitioned problem, provided the partition assigns equal
costs to equal actions.
-/
lemma genuine_landmark_partition_transfer {n P : ℕ} (prob : PlanningTask n)
    (partitioning : cost_partitioning prob P) (p : Fin P) (lm : List (Action n))
    (hlm : ∀ a ∈ lm, a ∈ prob.actions')
    (hpart : ∀ (i j : Fin prob.actions'.length), prob.actions'[i] = prob.actions'[j] →
      partitioning p i = partitioning p j)
    (h : is_disjunctive_action_landmark_for_state prob lm prob.init') :
    is_disjunctive_action_landmark_for_state (partition_STRIPS prob partitioning p)
      (lm.map (adapt_cost_of_action_to_partition prob partitioning p)) prob.init' := by
  refine' ⟨ _, _ ⟩
  · simp [ List.all_eq_true, PlanningTask.actions ]
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
    use Action.mk a0.name a0.pre a0.add a0.del (partitioning p i)
    refine' ⟨ _, _ ⟩
    · unfold adapt_cost_of_action_to_partition; simp
      grind
    · exact hi'

theorem lmcut_step_yields_non_zero_heuristic {n : ℕ} (prob : PlanningTask n)
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
        obtain ⟨a0, ha0⟩ : ∃ a0 : {b : Action n // b ∈ prob.actions'}, ft.1 = (↑(pcf a0) : Fin n) ∧ ft.2 ∈ a0.val.add.toList.toFinset := by
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
private lemma lmcut_step_landmark_ne_nil {n : ℕ} (prob : PlanningTask n)
    (u_g : unitary_goal prob) (pcf : precondition_choice_function prob)
    (hpos : 0 < (lmcut_step prob u_g pcf).2.1) : (lmcut_step prob u_g pcf).1 ≠ [] := by
  contrapose! hpos; unfold lmcut_step at *; simp_all

/-
The step value `minCost` is a lower bound on the cost of every action of the cut-induced
landmark (it is, by definition, the minimum of their costs).
-/
private lemma lmcut_step_value_le_cost_of_mem {n : ℕ} (prob : PlanningTask n) (u_g : unitary_goal prob)
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
private lemma lmcut_part0_action_invariant {n : ℕ} (prob : PlanningTask n) (u_g : unitary_goal prob)
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
private lemma lmcut_adapt_cost_eq {n : ℕ} (prob : PlanningTask n) (u_g : unitary_goal prob)
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
theorem lmcut_step_yields_landmark_with_heuristic_in_partition {n : ℕ} (prob : PlanningTask n)
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
  have key : (((get_all_equiv_delete_relaxed_actions prob (lmcut_step prob u_g pcf).1).map
        (adapt_cost_of_action_to_partition prob (lmcut_step prob u_g pcf).2.2 ⟨0, by omega⟩)).map
        (fun a => a.cost)).min (by simpa using hlm'_ne) = (lmcut_step prob u_g pcf).2.1 := by
    apply list_min_const
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
    exact lmcut_adapt_cost_eq prob u_g pcf a ha
  unfold elementary_landmark_heuristic
  rw [if_pos hgen, dif_neg hlm'_ne]
  exact (congrArg (fun x : ℕ => (x : ℕ∞)) key).symm

/-
The total action cost of `subprob = partition_STRIPS prob (lmcut_step …).2.2 1` is strictly
smaller than that of `prob`, provided the step's value `minCost` is positive: every landmark
action (there is at least one, since `minCost > 0` forces a nonempty landmark) has its cost in
partition `1` reduced by `minCost`, while no action's cost increases. This is the measure that
makes `lmcut_inner` terminate.
-/
lemma lmcut_step_subprob_sum_lt {n : ℕ} (prob : PlanningTask n) (u_g : unitary_goal prob)
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

def lmcut_inner {n : ℕ} (prob : PlanningTask n)
    (u_i : unitary_init prob)
    (u_g : unitary_goal prob)
    (hp : has_preconditions prob)
    (pcf : Π p : PlanningTask n, has_preconditions p → precondition_choice_function p):
      List (List (Action n)) × ℕ∞ × Σ p : ℕ, (cost_partitioning prob p) :=

    let jg := justification_graph prob (pcf prob hp)
    let i := (get_unitary_init prob u_i)
    let goal := (get_unitary_goal prob u_g)

    -- return no partitioning (`cost_partitioning prob 0` is the empty family); the problem is
    -- unsolvable, so the heuristic value is `⊤` (infinity)
    if ¬ reachable jg i goal then ([[]], ⊤ , ⟨0, fun p => p.elim0⟩)
    -- return no partitioning
    else if zero_cost_reachable jg i goal then ([], 0, ⟨0, fun p => p.elim0⟩)
    else
     let r := lmcut_step prob u_g (pcf prob hp)
     let subprob := partition_STRIPS prob r.2.2 ⟨1, by omega⟩

     let subret := lmcut_inner subprob u_i u_g
       (partition_STRIPS_has_preconditions prob r.2.2 ⟨1, by omega⟩ hp) pcf

     let lms : List (List (Action n)):= r.1 :: subret.1
     let hval : ℕ∞ := (r.2.1 : ℕ∞) + subret.2.1
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
    exact ⟨⟨w.bypass, WeightedDiGraph.Walk.bypass_isPath w⟩, fun u _ => by simp [NatGraph.hsearch_expandable]⟩
  unfold reachable
  cases h : NatGraph.astar (g := g) (fun _ => 0) v goal with
  | none => rw [h] at hcomplete; simp at hcomplete
  | some p => rfl

/-
If the unitary goal is not reachable from the unitary initial fact in the justification graph,
then the problem has no plan at all.  A real plan relaxes (via `relax_path`) to a delete-relaxed
path reaching the goal fact, and replaying that path in the justification graph
(`jgraph_reach_of_dr_path`, with the empty cut) witnesses reachability of the goal fact from the
initial fact — contradicting the assumption.
-/
lemma lmcut_no_plan_of_not_reachable {n : ℕ} (prob : PlanningTask n) (u_i : unitary_init prob)
    (u_g : unitary_goal prob) (pcf : precondition_choice_function prob)
    (h : ¬ reachable (justification_graph prob pcf)
      (get_unitary_init prob u_i) (get_unitary_goal prob u_g)) :
    IsEmpty (PlanningTask.Plan prob prob.init) := by
  refine ⟨fun plan => ?_⟩
  apply h
  -- Relax the real plan to a delete-relaxed path reaching a goal-satisfying state.
  obtain ⟨t2, ht2, q, _hq⟩ := relax_path prob plan.path (subset_refl prob.init)
  -- The unitary initial fact reaches itself (empty walk); the empty cut removes nothing.
  have hsrc : ∀ s ∈ prob.init,
      Nonempty ((remove_edges (justification_graph prob pcf) []).Walk
        (get_unitary_init prob u_i) s) := by
    intro s hs
    rw [get_unitary_init_is_init prob u_i, Set.mem_singleton_iff] at hs
    subst hs
    exact ⟨WeightedDiGraph.Walk.nil⟩
  -- The unitary goal fact is true at the end of the relaxed path.
  have hgoal_mem : get_unitary_goal prob u_g ∈ t2 := by
    apply ht2
    apply plan.goal
    rw [mem_convertVarSet]
    have hg := get_unitary_goal_is_goal prob u_g
    rw [VarSet.toList] at hg
    rw [hg]
    exact List.mem_singleton.mpr rfl
  -- Replaying the relaxed path in the (empty-cut) justification graph reaches the goal fact.
  obtain ⟨w⟩ := jgraph_reach_of_dr_path prob pcf [] (get_unitary_init prob u_i) q
    (by intro a0 _ y _; simp) hsrc (get_unitary_goal prob u_g) hgoal_mem
  exact reachable_of_walk _ (walk_of_remove_edges_walk _ [] w)

lemma path_transfer_to_partition {n P : ℕ} (prob : PlanningTask n)
    (partitioning : cost_partitioning prob P) (p : Fin P)
    {s1 s2 : State n} (path : PlanningTask.Path prob s1 s2) :
    ∃ path' : PlanningTask.Path (partition_STRIPS prob partitioning p) s1 s2,
      path'.actionsUsed
        = path.actionsUsed.map (adapt_cost_of_action_to_partition prob partitioning p) := by
          induction' path with s1 s2 path ih;
          · exact ⟨ PlanningTask.Path.empty _, rfl ⟩;
          · rename_i h₁ h₂ h₃;
            obtain ⟨ path', hpath' ⟩ := h₃;
            use PlanningTask.Path.cons (adapt_cost_of_action_to_partition prob partitioning p s2) ih (by
            -- Since s2 is in the original actions, and the adapted action is just s2 with the cost adjusted, it should be in the partitioned actions as well.
            simp [adapt_cost_of_action_to_partition, partition_STRIPS];
            split_ifs <;> simp_all +decide [ PlanningTask.actions ];
            · grind;
            · exact absurd ‹_› ( not_le_of_gt ( List.idxOf_lt_length_iff.mpr ‹_› ) )) (by
            unfold adapt_cost_of_action_to_partition; simp_all +decide [PlanningTask.actions];
            split_ifs <;> simp_all +decide [ Successor ];
            exact ⟨ h₁.1, rfl ⟩) path'
            generalize_proofs at *;
            simp +decide [ PlanningTask.Path.actionsUsed, hpath' ]

lemma plan_transfer_to_partition {n P : ℕ} (prob : PlanningTask n)
    (partitioning : cost_partitioning prob P) (p : Fin P)
    (plan : PlanningTask.Plan prob prob.init) :
    ∃ plan' : PlanningTask.Plan (partition_STRIPS prob partitioning p)
        (partition_STRIPS prob partitioning p).init,
      plan'.path.cost = (plan.path.actionsUsed.map
        (fun a => (adapt_cost_of_action_to_partition prob partitioning p a).cost)).sum := by
          obtain ⟨path', hpath'⟩ := path_transfer_to_partition prob partitioning p plan.path
          use ⟨plan.last, path', by
            exact fun x hx => plan.goal <| by simpa using hx;⟩
          generalize_proofs at *;
          rw [ path_cost_eq_sum_actionsUsed, hpath', List.map_map ];
          rfl

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
lemma lmcut_inner_value_zero {n : ℕ} (prob : PlanningTask n) (u_i : unitary_init prob)
    (u_g : unitary_goal prob) (hp : has_preconditions prob)
    (pcf : Π p : PlanningTask n, has_preconditions p → precondition_choice_function p)
    (hr : reachable (justification_graph prob (pcf prob hp))
      (get_unitary_init prob u_i) (get_unitary_goal prob u_g))
    (hz : zero_cost_reachable (justification_graph prob (pcf prob hp))
      (get_unitary_init prob u_i) (get_unitary_goal prob u_g)) :
    (lmcut_inner prob u_i u_g hp pcf).2.1 = 0 := by
  rw [lmcut_inner]
  simp [hr, hz]

/-- The value returned by `lmcut_inner` in the recursive branch: the step value plus the value of
the recursive call on the subproblem. -/
lemma lmcut_inner_value_step {n : ℕ} (prob : PlanningTask n) (u_i : unitary_init prob)
    (u_g : unitary_goal prob) (hp : has_preconditions prob)
    (pcf : Π p : PlanningTask n, has_preconditions p → precondition_choice_function p)
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

/-
Pointwise validity of the two-part `lmcut_step` partitioning after cost adaptation: for every
action of `prob`, its partition-`0` and partition-`1` adapted costs sum to at most its real cost.
-/
private lemma lmcut_adapt_cost_sum_le {n : ℕ} (prob : PlanningTask n) (u_g : unitary_goal prob)
    (pcf : precondition_choice_function prob) {a : Action n} (ha : a ∈ prob.actions') :
    (adapt_cost_of_action_to_partition prob (lmcut_step prob u_g pcf).2.2 ⟨0, by omega⟩ a).cost
      + (adapt_cost_of_action_to_partition prob (lmcut_step prob u_g pcf).2.2 ⟨1, by omega⟩ a).cost
      ≤ a.cost := by
        have := lmcut_step_yields_partitioning prob u_g pcf ⟨ List.idxOf a prob.actions', List.idxOf_lt_length_of_mem ha ⟩ ; simp_all +decide [ List.finRange ] ;
        grind +suggestions

/-
Strong-induction skeleton for `lmcut_inner_admissible_for_init`.
-/
lemma lmcut_inner_admissible_aux {n : ℕ}
    (pcf : Π p : PlanningTask n, has_preconditions p → precondition_choice_function p) (M : ℕ) :
    ∀ (prob : PlanningTask n) (u_i : unitary_init prob) (u_g : unitary_goal prob)
      (hp : has_preconditions prob),
      (prob.actions'.map (fun a => a.cost)).sum = M →
      ∀ plan : PlanningTask.Plan prob prob.init, plan.path.cost ≥ (lmcut_inner prob u_i u_g hp pcf).2.1 := by
        induction' M using Nat.strong_induction_on with M ih;
        -- Start the proof by introducing `prob, u_i, u_g, hp, hM, plan` and opening the `lmcut_inner` definition using its termination measure.
        -- This will expose the three cases for `hr: reachable ... goal`, which can be handled with ` lmcut_no_plan_of_not_reachable` and `lmcut_inner_value_zero`/` isotone`.
        intro prob u_i u_g hp hM plan
        rw [lmcut_inner]
        -- Now we can `simp` to unfold the `if` and work with reachable and zero-cost reachability conditions.;
        split_ifs;
        · exact Nat.cast_nonneg _;
        · obtain ⟨plan0, hplan0⟩ := plan_transfer_to_partition prob (lmcut_step prob u_g (pcf prob hp)).2.2 ⟨0, by omega⟩ plan
          obtain ⟨plan1, hplan1⟩ := plan_transfer_to_partition prob (lmcut_step prob u_g (pcf prob hp)).2.2 ⟨1, by omega⟩ plan;
          -- By `elementary_landmark_heuristic_is_admissible`, we have `(r.2.1 : ℕ∞) ≤ (plan0.path.cost : ℕ∞)`.
          have hplan0_cost : (lmcut_step prob u_g (pcf prob hp)).2.1 ≤ (plan0.path.cost : ℕ∞) := by
            have := lmcut_step_yields_landmark_with_heuristic_in_partition prob u_i u_g (pcf prob hp) ‹_› ‹_›;
            rw [this];
            apply elementary_landmark_heuristic_is_admissible;
          have hplan1_cost : (lmcut_inner (partition_STRIPS prob (lmcut_step prob u_g (pcf prob hp)).2.2 ⟨1, by omega⟩) u_i u_g (partition_STRIPS_has_preconditions prob (lmcut_step prob u_g (pcf prob hp)).2.2 ⟨1, by omega⟩ hp) pcf).2.1 ≤ (plan1.path.cost : ℕ∞) := by
            apply ih;
            exact lmcut_step_subprob_sum_lt prob u_g ( pcf prob hp ) ( lmcut_step_yields_non_zero_heuristic prob u_i u_g ( pcf prob hp ) ‹_› ‹_› ) |> lt_of_lt_of_le <| hM.le;
            rfl;
          have hplan_cost : (plan.path.actionsUsed.map (fun a => a.cost)).sum ≥ (plan0.path.cost : ℕ) + (plan1.path.cost : ℕ) := by
            rw [hplan0, hplan1];
            apply list_sum_map_add_le;
            exact fun a ha => lmcut_adapt_cost_sum_le prob u_g ( pcf prob hp ) ( mem_actions_of_mem_actionsUsed _ ha |> List.mem_toFinset.mp );
          exact le_trans ( add_le_add hplan0_cost hplan1_cost ) ( mod_cast hplan_cost.trans ( mod_cast path_cost_eq_sum_actionsUsed plan.path ▸ le_rfl ) );
        · exact False.elim <| lmcut_no_plan_of_not_reachable prob u_i u_g ( pcf prob hp ) ‹_› |>.false plan

lemma lmcut_inner_admissible_for_init {n : ℕ} (prob : PlanningTask n)
    (u_i : unitary_init prob)
    (u_g : unitary_goal prob)
    (hp : has_preconditions prob)
    (pcf : Π p : PlanningTask n, has_preconditions p → precondition_choice_function p):
      ∀ plan : PlanningTask.Plan prob prob.init, plan.path.cost ≥ (lmcut_inner prob u_i u_g hp pcf).2.1 :=
  lmcut_inner_admissible_aux pcf _ prob u_i u_g hp rfl