import Mathlib.Tactic.Cases

import planning.Planning

namespace STRIPS


private lemma getElem_eq_rec_BitVec {m n : ℕ} (h : m = n) (bv : BitVec m) (i : ℕ)
    (hi : i < n) :
    (show BitVec n from h ▸ bv)[i] = bv[i]'(by omega) := by
  subst h; rfl

def h_1_base (n : ℕ) (s : BitVec n) : Vector (WithTop ℕ) n :=
    (Vector.finRange n).map (fun i => if s[i] then some 0 else none)


def vec_to_state (n : ℕ) (bef : Vector (WithTop ℕ) n) : BitVec n :=
  let l_bool : List Bool := (bef.map (fun x => x.isSome)).toList
  have l_bool_len : l_bool.length = n := by grind
  l_bool_len ▸ BitVec.ofBoolListLE l_bool

lemma vec_to_state_getElem (n : ℕ) (bef : Vector (WithTop ℕ) n) (i : Fin n) :
    (vec_to_state n bef)[i.val] = (bef[i]).isSome := by
  unfold vec_to_state;
  grind +suggestions

lemma vec_to_state_isSome_of_satisfies (n : ℕ) (bef : Vector (WithTop ℕ) n)
    (cond : VarSet n) (h : satisfies' cond (vec_to_state n bef) = true)
    (i : Fin n) (hi : i ∈ cond.val) : (bef[i]).isSome = true := by
  have := (satisfies'_iff cond (vec_to_state n bef)).mp h i hi
  rw [← vec_to_state_getElem]
  exact this

lemma vec_to_state_isSome_of_applicable (n : ℕ) (bef : Vector (WithTop ℕ) n)
    (a : Action n) (h : applicable' a (vec_to_state n bef) = true)
    (i : Fin n) (hi : i ∈ a.pre.toList) : (bef[i]).isSome = true :=
  vec_to_state_isSome_of_satisfies n bef a.pre h i (VarSet.mem_toList.mp hi)

/-- Compare a new cost with the current best: update if the new cost is strictly cheaper. -/
def updateIfCheaper (newCost : ℕ) (current : WithTop ℕ) : WithTop ℕ :=
  match current with
  | none => some newCost         -- current = ⊤, any finite cost is better
  | some v => if newCost < v then some newCost else current

/-- Corrected `h_1_step`: uses `updateIfCheaper` to compare the newly computed cost with the
current best value, instead of with the fact index. -/
def h_1_step (n : ℕ) (prob : PlanningTask n) (bef : Vector (WithTop ℕ) n) : Vector (WithTop ℕ) n :=
  let s_b := vec_to_state n bef
  -- update the values of each fact
  (Vector.finRange n).map (fun i : Fin n =>
    let applicable : List ℕ := prob.actions'.filterMap (fun a =>
    if i ∈ a.add.toList then -- consider only actions that add the fact i. We ignore delete effects
      if is_appli : applicable' a s_b then
        let pre_cost : List ℕ := a.pre.toList.attach.map (fun x : { x : Fin n // x ∈ a.pre.toList } =>
          bef[x.1].get (by exact vec_to_state_isSome_of_applicable n bef a is_appli x.1 x.2))

        -- cost of the action plus most expensive precondition
        if pre_cost_nil : pre_cost = [] then .some (a.cost)
        else
          let preMax : ℕ := pre_cost.max pre_cost_nil
          .some (a.cost + preMax)
      else .none -- action not applicable given the facts that are currently .some
    else .none)

    if appli_nil : applicable = [] then bef[i]
    else
      let minCost : ℕ := applicable.min appli_nil
      updateIfCheaper minCost bef[i]
  )


---- h_1 effectively considers delete relaxation
--def h_1 {n : ℕ} (prob : PlanningTask n) (s : BitVec n) : ℕ :=
--  let f : Vector (WithTop ℕ) n → Fin (prob.actions'.length) → Vector (WithTop ℕ) n := fun a _ =>
--    h_1_step n prob a
--  let result := (List.finRange prob.actions'.length).foldl f (h_1_base n s)
--  let s_b := vec_to_state n result
--
--  -- check if the goal has been reached
--  if h_sat : satisfies' prob.goal' s_b then
--    let pre_cost : List ℕ := prob.goal'.toList.attach.map (fun x : { x : Fin n // x ∈ prob.goal'.toList } =>
--      result[x.1].get (by exact vec_to_state_isSome_of_satisfies n result prob.goal' h_sat x.1 x.2))
--
--    -- cost of the action plus most expensive precondition
--    if pre_cost_nil : pre_cost = [] then 0 else pre_cost.max pre_cost_nil
--  else
--    ⊤ -- state is unsolvable (heuristic value is infinity)

/-- `updateIfCheaper` never increases the value. -/
lemma updateIfCheaper_le (c : ℕ) (v : WithTop ℕ) : updateIfCheaper c v ≤ v := by
  cases v with
  | top => exact le_top
  | coe val =>
    simp [updateIfCheaper]
    split_ifs with h
    · exact WithTop.coe_le_coe.mpr (Nat.le_of_lt h)
    · rfl

/-- `updateIfCheaper` always produces a `some` value. -/
lemma updateIfCheaper_isSome (c : ℕ) (v : WithTop ℕ) :
    (updateIfCheaper c v).isSome = true := by
  cases v with
  | top => rfl
  | coe val => simp only [updateIfCheaper]; split_ifs <;> rfl

/-- `updateIfCheaper` value is at most c. -/
lemma updateIfCheaper_le_newCost (c : ℕ) (v : WithTop ℕ) :
    updateIfCheaper c v ≤ some c := by
  cases v with
  | top => simp [updateIfCheaper]
  | coe val =>
    simp [updateIfCheaper]
    split_ifs with h
    · rfl
    · push Not at h; exact WithTop.coe_le_coe.mpr h

/-- If `updateIfCheaper` changes the current value, the result is exactly `some` of the new cost. -/
lemma updateIfCheaper_eq_some_of_ne (c : ℕ) (v : WithTop ℕ) (h : updateIfCheaper c v ≠ v) :
    updateIfCheaper c v = some c := by
  cases v with
  | top => rfl
  | coe val =>
    simp only [updateIfCheaper] at h ⊢
    split_ifs at h ⊢ with hlt
    · rfl
    · exact absurd rfl h

/-- The value of `h_1_step` at a single index `i`, with the outer `Vector.map`/`finRange` resolved.
This exposes the `filterMap`/`updateIfCheaper`/`min` structure as a plain term, so that lemmas about
the step can reason by list manipulation instead of re-unfolding the definition. -/
lemma h_1_step_getElem (n : ℕ) (prob : PlanningTask n) (bef : Vector (WithTop ℕ) n) (i : Fin n) :
    (h_1_step n prob bef)[i] =
      (let applicable : List ℕ := prob.actions'.filterMap (fun a =>
        if i ∈ a.add.toList then
          if is_appli : applicable' a (vec_to_state n bef) then
            let pre_cost : List ℕ := a.pre.toList.attach.map (fun x : { x : Fin n // x ∈ a.pre.toList } =>
              bef[x.1].get (vec_to_state_isSome_of_applicable n bef a is_appli x.1 x.2))
            if pre_cost_nil : pre_cost = [] then .some (a.cost)
            else .some (a.cost + pre_cost.max pre_cost_nil)
          else .none
        else .none)
      if appli_nil : applicable = [] then bef[i]
      else updateIfCheaper (applicable.min appli_nil) bef[i]) := by
  unfold h_1_step
  simp only [Fin.getElem_fin, Vector.getElem_map, Vector.getElem_finRange]

/-- Monotonicity: `h_1_step` only decreases values (in the `WithTop ℕ` order). -/
lemma h_1_step_le (n : ℕ) (prob : PlanningTask n) (bef : Vector (WithTop ℕ) n) (i : Fin n) :
    (h_1_step n prob bef)[i] ≤ bef[i] := by
      unfold h_1_step;
      simp +zetaDelta at *;
      split_ifs <;> [ rfl; exact updateIfCheaper_le _ _ ]

/-- After k foldl iterations, the vector values are non-increasing compared to the base. -/
lemma h_1_foldl_le {n : ℕ} (prob : PlanningTask n) (s : BitVec n) (l : List (Fin prob.actions'.length))
    (i : Fin n) :
    (l.foldl (fun a _ => h_1_step n prob a) (h_1_base n s))[i] ≤ (h_1_base n s)[i] := by
      induction l using List.reverseRecOn <;> simp_all [ List.foldl ];
      exact le_trans ( h_1_step_le _ _ _ _ ) ‹_›

/-- The base values are admissible: if initially some c, then c = 0 ≤ path.cost.
NOTE: lemma produced by Aristotle, but useless. It only holds for c = 0 and otherwise vacuous -/
lemma h_1_base_admissible {n : ℕ} (prob : PlanningTask n) (s : BitVec n)
    (i : Fin n) (c : ℕ) (h_val : (h_1_base n s)[i] = some c)
    (goal : BitVec n)
    (path : WeightedDiGraph.Path (G := trans_of_STRIPS prob) s goal) :
    c ≤ path.cost := by
      unfold h_1_base at h_val;
      grind

/-
If an action is applicable in the current state and adds fact i, then fact i becomes
    discovered (isSome) after h_1_step.
-/
lemma h_1_step_discovers {n : ℕ} (prob : PlanningTask n) (bef : Vector (WithTop ℕ) n)
    (i : Fin n) (a : Action n) (ha : a ∈ prob.actions')
    (hadd : i ∈ a.add.toList)
    (hpre : ∀ j ∈ a.pre.toList, (bef[j]).isSome = true) :
    ((h_1_step n prob bef)[i]).isSome = true := by
      unfold h_1_step;
      unfold updateIfCheaper;
      have h_applicable : applicable' a (vec_to_state n bef) = true := by
        unfold applicable';
        unfold satisfies';
        simp_all [ vec_to_state_getElem ];
      grind

/-- After applying h_1_step, all previously discovered facts remain discovered. -/
lemma h_1_step_preserves_isSome {n : ℕ} (prob : PlanningTask n) (bef : Vector (WithTop ℕ) n)
    (i : Fin n) (h : (bef[i]).isSome = true) :
    ((h_1_step n prob bef)[i]).isSome = true := by
  have h_le := h_1_step_le n prob bef i
  cases h_eq : bef[i] with
  | top => exact absurd h (by rw [h_eq]; decide)
  | coe c =>
    rw [h_eq] at h_le
    cases h_step : (h_1_step n prob bef)[i] with
    | top => rw [h_step] at h_le; simp at h_le
    | coe _ => rfl

/-- After k iterations of h_1_step, previously discovered facts remain discovered. -/
lemma h_1_foldl_preserves_isSome {n : ℕ} (prob : PlanningTask n) (base : Vector (WithTop ℕ) n)
    (l : List α) (i : Fin n) (h : (base[i]).isSome = true) :
    ((l.foldl (fun a _ => h_1_step n prob a) base)[i]).isSome = true := by
      induction l generalizing base <;> simp_all;
      rename_i _ _ ih
      exact ih _ ( h_1_step_preserves_isSome prob base i h )

/-- After k iterations, if fact i is true in state v, then bef[i].isSome. -/
lemma h_1_foldl_true_in_v_isSome {n : ℕ} (prob : PlanningTask n) (v : BitVec n)
    (l : List (Fin prob.actions'.length))
    (i : Fin n) (hvi : v[i.val] = true) :
    ((l.foldl (fun a _ => h_1_step n prob a) (h_1_base n v))[i]).isSome = true := by
  apply h_1_foldl_preserves_isSome
  unfold h_1_base
  simp [hvi]

/-
At a fixpoint, a walk from s to goal ensures all goal-facts are isSome in bef.
-/
set_option maxHeartbeats 2000000 in
lemma walk_at_fixpoint_goal_isSome {n : ℕ} (prob : PlanningTask n) (bef : Vector (WithTop ℕ) n)
    (hfix : ∀ a ∈ prob.actions', applicable' a (vec_to_state n bef) = true →
      ∀ i ∈ a.add.toList, (bef[i]).isSome = true)
    {s goal : BitVec n} (w : (trans_of_STRIPS prob).Walk s goal)
    (hs : ∀ i : Fin n, s[i.val] = true → (bef[i]).isSome = true)
    (j : Fin n) (hj : goal[j.val] = true) :
    (bef[j]).isSome = true := by
  induction' w with u v w ih;
  · exact hs j hj;
  · obtain ⟨a, ha, hadd⟩ : ∃ a ∈ prob.actions', applicable' a v ∧ is_successor' a v w := by
      (expose_names; exact List.any_iff_exists_prop.mp h);
    unfold applicable' at hadd; simp_all +decide [ satisfies'_iff ] ;
    unfold is_successor' at hadd; simp_all +decide [ successor' ] ;
    grind +suggestions

lemma h_1_step_applicable_effects {n : ℕ} (prob : PlanningTask n) (bef : Vector (WithTop ℕ) n)
    (a : Action n) (ha : a ∈ prob.actions')
    (happ : applicable' a (vec_to_state n bef) = true)
    (i : Fin n) (hi : i ∈ a.add.toList) :
    ((h_1_step n prob bef)[i]).isSome = true := by
  apply h_1_step_discovers prob bef i a ha hi
  intro j hj
  exact vec_to_state_isSome_of_applicable n bef a happ j hj

/-
The isSome pattern of h_1_step depends only on vec_to_state.
-/
lemma h_1_step_isSome_determined {n : ℕ} (prob : PlanningTask n) (bef1 bef2 : Vector (WithTop ℕ) n)
    (heq : vec_to_state n bef1 = vec_to_state n bef2)
    (i : Fin n) :
    ((h_1_step n prob bef1)[i]).isSome = ((h_1_step n prob bef2)[i]).isSome := by
      have h_isSome_eq : ((h_1_step n prob bef1)[i]).isSome = true ↔ ((h_1_step n prob bef2)[i]).isSome = true := by
        by_cases h : ∃ a : Action n, a ∈ prob.actions' ∧ i ∈ a.add.toList ∧ applicable' a (vec_to_state n bef1) = true <;> simp_all
        · obtain ⟨ a, ha, hi, ha' ⟩ := h; have := h_1_step_applicable_effects prob bef1 a; have := h_1_step_applicable_effects prob bef2 a; simp_all
        · unfold h_1_step;
          rw [ Vector.getElem_map, Vector.getElem_map ];
          simp +zetaDelta at *;
          have := vec_to_state_getElem n bef1 i; have := vec_to_state_getElem n bef2 i;
          simp_all only [Fin.getElem_fin, Bool.false_eq_true, IsEmpty.forall_iff, implies_true,
      ↓reduceDIte]
      grind

/-- Once the isSome pattern stabilizes, it stays stable. -/
lemma h_1_step_stable_isSome {n : ℕ} (prob : PlanningTask n) (bef : Vector (WithTop ℕ) n)
    (i : Fin n)
    (hstable : vec_to_state n (h_1_step n prob bef) = vec_to_state n bef) :
    ((h_1_step n prob (h_1_step n prob bef))[i]).isSome =
    ((h_1_step n prob bef)[i]).isSome := by
  exact h_1_step_isSome_determined prob (h_1_step n prob bef) bef hstable i

/-
If an applicable action's effect is NOT isSome in bef, then h_1_step discovers new facts.
-/
lemma h_1_step_changes_if_not_fixpoint {n : ℕ} (prob : PlanningTask n) (bef : Vector (WithTop ℕ) n)
    (a : Action n) (ha : a ∈ prob.actions')
    (happ : applicable' a (vec_to_state n bef) = true)
    (i : Fin n) (hi : i ∈ a.add.toList) (hnot : (bef[i]).isSome = false) :
    vec_to_state n (h_1_step n prob bef) ≠ vec_to_state n bef := by
      have h_step_some : ((h_1_step n prob bef)[i]).isSome = true := by
        exact h_1_step_applicable_effects prob bef a ha happ i hi;
      intro H; have := vec_to_state_getElem n ( h_1_step n prob bef ) i; have := vec_to_state_getElem n bef i
      simp_all only [Fin.getElem_fin, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none, Option.isSome_none, Bool.false_eq_true]

/-
If vec_to_state changes, then the applicable filter grows.
-/
lemma applicable_filter_grows {n : ℕ} (prob : PlanningTask n)
    (bef_prev bef : Vector (WithTop ℕ) n)
    (hstep : bef = h_1_step n prob bef_prev)
    (hchanged : vec_to_state n (h_1_step n prob bef) ≠ vec_to_state n bef) :
    (prob.actions'.filter (fun a => applicable' a (vec_to_state n bef))).length >
    (prob.actions'.filter (fun a => applicable' a (vec_to_state n bef_prev))).length := by
      have h_filter_superset : ∀ a ∈ prob.actions',
          applicable' a (vec_to_state n bef_prev) → applicable' a (vec_to_state n bef) := by
        intros a ha happ
        rw [applicable'_iff] at happ ⊢
        intro i hi
        have hp := happ i hi
        rw [vec_to_state_getElem] at hp ⊢
        rw [hstep]
        exact h_1_step_preserves_isSome prob bef_prev i hp
      have h_filter_length : ∃ a ∈ prob.actions',
          applicable' a (vec_to_state n bef) ∧ ¬applicable' a (vec_to_state n bef_prev) := by
        contrapose! hchanged
        have h_filter_eq : ∀ i : Fin n,
            (h_1_step n prob bef)[i].isSome = (bef)[i].isSome := by
          intro i
          by_cases h_add : ∃ a ∈ prob.actions',
              applicable' a (vec_to_state n bef) ∧ i ∈ a.add.toList
          · obtain ⟨ a, ha₁, ha₂, ha₃ ⟩ := h_add
            have h_filter_eq : (bef)[i].isSome = true := by
              have := h_1_step_applicable_effects prob bef_prev a ha₁
                ( hchanged a ha₁ ha₂ ) i ha₃
              simp_all only [Fin.getElem_fin]
            rw [ h_1_step_preserves_isSome ]
            subst hstep
            simp_all only [Fin.getElem_fin]
            exact h_filter_eq
          · rw [h_1_step_getElem]
            push Not at h_add
            rw [dif_pos (by
              apply List.filterMap_eq_nil_iff.mpr
              intro a ha
              by_cases hadd : i ∈ a.add.toList
              · by_cases happ : applicable' a (vec_to_state n bef)
                · exact absurd hadd (h_add a ha happ)
                · simp [hadd, happ]
              · simp [hadd])]
        ext i
        convert h_filter_eq ⟨ i, by assumption ⟩ using 1
        · convert vec_to_state_getElem n ( h_1_step n prob bef ) ⟨ i, by assumption ⟩ using 1
        · convert vec_to_state_getElem n bef ⟨ i, by assumption ⟩ using 1
      have h_perm : List.Perm
          (List.filter (fun a => applicable' a (vec_to_state n bef)) prob.actions')
          (List.filter (fun a => applicable' a (vec_to_state n bef_prev)) prob.actions' ++
            List.filter (fun a => applicable' a (vec_to_state n bef) ∧
              ¬applicable' a (vec_to_state n bef_prev)) prob.actions') := by
        rw [ List.perm_iff_count ]
        intro a
        have key : ∀ (p : Action n → Bool) (l : List (Action n)),
            List.count a (l.filter p) = if p a then List.count a l else 0 := by
          intro p l
          induction l with
          | nil => simp
          | cons x xs ih =>
            rw [List.filter_cons]
            by_cases hx : p x <;> by_cases hpa : p a <;> by_cases hax : a = x <;>
              simp_all [@eq_comm _ x a]
        simp only [List.count_append, key]
        by_cases ha : a ∈ prob.actions'
        · have hsup := h_filter_superset a ha
          by_cases hP : applicable' a (vec_to_state n bef) = true <;>
            by_cases hQ : applicable' a (vec_to_state n bef_prev) = true <;>
            simp_all
        · simp [List.count_eq_zero_of_not_mem ha]
      have hlen := h_perm.length_eq
      simp only [List.length_append] at hlen
      obtain ⟨a, ha, ha1, ha2⟩ := h_filter_length
      have hpos : 0 < (List.filter (fun a => applicable' a (vec_to_state n bef) ∧
          ¬applicable' a (vec_to_state n bef_prev)) prob.actions').length := by
        rw [List.length_pos_iff_exists_mem]
        exact ⟨a, by simp [List.mem_filter, ha, ha1, ha2]⟩
      omega

lemma stable_implies_fixpoint {n : ℕ} (prob : PlanningTask n) (bef : Vector (WithTop ℕ) n)
    (hstable : vec_to_state n (h_1_step n prob bef) = vec_to_state n bef) :
    ∀ a ∈ prob.actions', applicable' a (vec_to_state n bef) = true →
      ∀ i ∈ a.add.toList, (bef[i]).isSome = true := by
  intro a ha happ i hi
  by_contra h
  simp at h
  exact absurd hstable (h_1_step_changes_if_not_fixpoint prob bef a ha happ i hi (by simp [h]))

/-
If the fixpoint property holds, then vec_to_state is stable.
-/
lemma fixpoint_implies_stable {n : ℕ} (prob : PlanningTask n) (bef : Vector (WithTop ℕ) n)
    (hfix : ∀ a ∈ prob.actions', applicable' a (vec_to_state n bef) = true →
      ∀ i ∈ a.add.toList, (bef[i]).isSome = true) :
    vec_to_state n (h_1_step n prob bef) = vec_to_state n bef := by
      have h_vec_to_state_eq : ∀ i : Fin n, (vec_to_state n (h_1_step n prob bef))[i.val] = (vec_to_state n bef)[i.val] := by
        intro i; by_cases hi : ( bef[i] ).isSome = true <;> simp_all [ vec_to_state_getElem ] ;
        · exact h_1_step_preserves_isSome prob bef i hi;
        · unfold h_1_step;
          simp [ hi, updateIfCheaper ];
          grind;
      ext i;
      exact h_vec_to_state_eq ⟨ i, by assumption ⟩

--/-
--The fixpoint property is persistent: once achieved, it holds at all subsequent iterations.
---/
--lemma fixpoint_persistent {n : ℕ} (prob : PlanningTask n) (base : Vector (WithTop ℕ) n)
--    (k : ℕ) (hfix : ∀ a ∈ prob.actions', applicable' a (vec_to_state n (h_1_iter prob base k)) = true →
--      ∀ i ∈ a.add.toList, ((h_1_iter prob base k)[i]).isSome = true)
--    (m : ℕ) (hm : m ≥ k) :
--    ∀ a ∈ prob.actions', applicable' a (vec_to_state n (h_1_iter prob base m)) = true →
--      ∀ i ∈ a.add.toList, ((h_1_iter prob base m)[i]).isSome = true := by
--        induction' hm with m hm ih;
--        · assumption;
--        · intro a ha h;
--          have h_eq : vec_to_state n (h_1_iter prob base (m + 1)) = vec_to_state n (h_1_iter prob base m) := by
--            exact fixpoint_implies_stable prob _ ih;
--          have h_eq : applicable' a (vec_to_state n (h_1_iter prob base m)) = true := by
--            grind;
--          exact fun i hi => h_1_step_preserves_isSome prob ( h_1_iter prob base m ) i ( ih a ha h_eq i hi )
--
end STRIPS
