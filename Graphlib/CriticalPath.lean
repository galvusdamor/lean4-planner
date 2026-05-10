import Mathlib.Tactic.Cases

import Graphlib.Planning

namespace Validator


private lemma getElem_eq_rec_BitVec {m n : ℕ} (h : m = n) (bv : BitVec m) (i : ℕ)
    (hi : i < n) :
    (show BitVec n from h ▸ bv)[i] = bv[i]'(by omega) := by
  subst h; rfl

def h_1_base (n : ℕ) (s : State' n) : Vector (WithTop ℕ) n :=
    (Vector.finRange n).map (fun i => if s[i] then some 0 else none)


def vec_to_state (n : ℕ) (bef : Vector (WithTop ℕ) n) : State' n :=
  let l_bool : List Bool := (bef.map (fun x => x.isSome)).toList
  have l_bool_len : l_bool.length = n := by grind
  l_bool_len ▸ BitVec.ofBoolListLE l_bool

lemma vec_to_state_getElem (n : ℕ) (bef : Vector (WithTop ℕ) n) (i : Fin n) :
    (vec_to_state n bef)[i.val] = (bef[i]).isSome := by
  unfold vec_to_state
  simp only
  rw [getElem_eq_rec_BitVec]
  rw [BitVec.getElem_ofBoolListLE]
  simp

lemma vec_to_state_isSome_of_satisfies (n : ℕ) (bef : Vector (WithTop ℕ) n)
    (cond : VarSet' n) (h : satisfies' cond (vec_to_state n bef) = true)
    (i : Fin n) (hi : i ∈ cond.val) : (bef[i]).isSome = true := by
  unfold satisfies' at h
  rw [List.all_eq_true] at h
  have := h i hi
  rw [← vec_to_state_getElem]
  exact this

lemma vec_to_state_isSome_of_applicable (n : ℕ) (bef : Vector (WithTop ℕ) n)
    (a : Action n) (h : applicable' a (vec_to_state n bef) = true)
    (i : Fin n) (hi : i ∈ a.pre'.val) : (bef[i]).isSome = true :=
  vec_to_state_isSome_of_satisfies n bef a.pre' h i hi

/-- Compare a new cost with the current best: update if the new cost is strictly cheaper. -/
private def updateIfCheaper (newCost : ℕ) (current : WithTop ℕ) : WithTop ℕ :=
  match current with
  | none => some newCost         -- current = ⊤, any finite cost is better
  | some v => if newCost < v then some newCost else current

/-- Corrected `h_1_step`: uses `updateIfCheaper` to compare the newly computed cost with the
current best value, instead of with the fact index. -/
def h_1_step (n : ℕ) (prob : STRIPS n) (bef : Vector (WithTop ℕ) n) : Vector (WithTop ℕ) n :=
  let s_b := vec_to_state n bef
  -- update the values of each fact
  (Vector.finRange n).map (fun i : Fin n =>
    let applicable : List ℕ := prob.actions'.filterMap (fun a =>
    if i ∈ a.add'.1 then -- consider only actions that add the fact i. We ignore delete effects
      if is_appli : applicable' a s_b then
        let pre_cost : List ℕ := a.pre'.1.attach.map (fun x : { x : Fin n // x ∈ a.pre'.1 } =>
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


-- h_1 effectively considers delete relaxation
def h_1 {n : ℕ} (prob : STRIPS n) (s : State' n) : ℕ :=
  let f : Vector (WithTop ℕ) n → Fin (prob.actions'.length) → Vector (WithTop ℕ) n := fun a _ =>
    h_1_step n prob a
  let result := (List.finRange prob.actions'.length).foldl f (h_1_base n s)
  let s_b := vec_to_state n result

  -- check if the goal has been reached
  if h_sat : satisfies' prob.goal' s_b then
    let pre_cost : List ℕ := prob.goal'.val.attach.map (fun x : { x : Fin n // x ∈ prob.goal'.val } =>
      result[x.1].get (by exact vec_to_state_isSome_of_satisfies n result prob.goal' h_sat x.1 x.2))

    -- cost of the action plus most expensive precondition
    if pre_cost_nil : pre_cost = [] then 0 else pre_cost.max pre_cost_nil
  else
    (2^n) * (max_action_cost prob) -- state is unsolvable

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
    · push_neg at h; exact WithTop.coe_le_coe.mpr h

/-- Monotonicity: `h_1_step` only decreases values (in the `WithTop ℕ` order). -/
lemma h_1_step_le (n : ℕ) (prob : STRIPS n) (bef : Vector (WithTop ℕ) n) (i : Fin n) :
    (h_1_step n prob bef)[i] ≤ bef[i] := by
      unfold h_1_step;
      simp +zetaDelta at *;
      split_ifs <;> [ rfl; exact updateIfCheaper_le _ _ ]

/-- After k foldl iterations, the vector values are non-increasing compared to the base. -/
lemma h_1_foldl_le {n : ℕ} (prob : STRIPS n) (s : State' n) (l : List (Fin prob.actions'.length))
    (i : Fin n) :
    (l.foldl (fun a _ => h_1_step n prob a) (h_1_base n s))[i] ≤ (h_1_base n s)[i] := by
      induction l using List.reverseRecOn <;> simp_all +decide [ List.foldl ];
      exact le_trans ( h_1_step_le _ _ _ _ ) ‹_›

/-- The base values are admissible: if initially some c, then c = 0 ≤ path.cost.
NOTE: lemma produced by Aristotle, but useless. It only holds for c = 0 and otherwise vacuous -/
lemma h_1_base_admissible {n : ℕ} (prob : STRIPS n) (s : State' n)
    (i : Fin n) (c : ℕ) (h_val : (h_1_base n s)[i] = some c)
    (goal : State' n)
    (path : WeightedDiGraph.Path (G := trans_of_STRIPS prob) s goal) :
    c ≤ path.cost := by
      unfold h_1_base at h_val;
      grind

/-
If an action is applicable in the current state and adds fact i, then fact i becomes
    discovered (isSome) after h_1_step.
-/
lemma h_1_step_discovers {n : ℕ} (prob : STRIPS n) (bef : Vector (WithTop ℕ) n)
    (i : Fin n) (a : Action n) (ha : a ∈ prob.actions')
    (hadd : i ∈ a.add'.val)
    (hpre : ∀ j ∈ a.pre'.val, (bef[j]).isSome = true) :
    ((h_1_step n prob bef)[i]).isSome = true := by
      unfold h_1_step;
      unfold updateIfCheaper;
      have h_applicable : applicable' a (vec_to_state n bef) = true := by
        unfold applicable';
        unfold satisfies';
        simp_all +decide [ vec_to_state_getElem ];
      grind

/-- After applying h_1_step, all previously discovered facts remain discovered. -/
lemma h_1_step_preserves_isSome {n : ℕ} (prob : STRIPS n) (bef : Vector (WithTop ℕ) n)
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
lemma h_1_foldl_preserves_isSome {n : ℕ} (prob : STRIPS n) (base : Vector (WithTop ℕ) n)
    (l : List α) (i : Fin n) (h : (base[i]).isSome = true) :
    ((l.foldl (fun a _ => h_1_step n prob a) base)[i]).isSome = true := by
      induction l generalizing base <;> simp_all +decide;
      rename_i _ _ ih
      exact ih _ ( h_1_step_preserves_isSome prob base i h )

/-- After k iterations, if fact i is true in state v, then bef[i].isSome. -/
lemma h_1_foldl_true_in_v_isSome {n : ℕ} (prob : STRIPS n) (v : State' n)
    (l : List (Fin prob.actions'.length))
    (i : Fin n) (hvi : v[i.val] = true) :
    ((l.foldl (fun a _ => h_1_step n prob a) (h_1_base n v))[i]).isSome = true := by
  apply h_1_foldl_preserves_isSome
  unfold h_1_base
  simp [hvi]

/-
At a fixpoint, a walk from s to goal ensures all goal-facts are isSome in bef.
-/
set_option maxHeartbeats 400000 in
lemma walk_at_fixpoint_goal_isSome {n : ℕ} (prob : STRIPS n) (bef : Vector (WithTop ℕ) n)
    (hfix : ∀ a ∈ prob.actions', applicable' a (vec_to_state n bef) = true →
      ∀ i ∈ a.add'.val, (bef[i]).isSome = true)
    {s goal : State' n} (w : (trans_of_STRIPS prob).Walk s goal)
    (hs : ∀ i : Fin n, s[i.val] = true → (bef[i]).isSome = true)
    (j : Fin n) (hj : goal[j.val] = true) :
    (bef[j]).isSome = true := by
      induction' w with s t w ih generalizing bef;
      · exact hs j hj;
      · rename_i h₁ h₂ h₃;
        apply h₃ bef hfix;
        · have := is_successor_state_of_trans_STRIPS_adj prob t w h₁;
          unfold is_successor_state at this; simp_all +decide [ List.any_eq_true ] ;
          obtain ⟨ a, ha₁, ha₂, ha₃ ⟩ := this; unfold is_successor' at ha₃; simp_all +decide [ List.all_eq_true ] ;
          intro i hi; specialize ha₃ i; split_ifs at ha₃ <;> simp_all +decide ;
          exact hfix a ha₁ ( by
            have h_applicable : ∀ i ∈ a.pre'.val, (vec_to_state n bef)[i] = true := by
              intro i hi; specialize hs i; simp_all +decide [ vec_to_state_getElem ] ;
              unfold applicable' at ha₂; simp_all +decide [ satisfies' ] ;
            unfold applicable' satisfies'
            simp_all only [Fin.getElem_fin, List.all_eq_true, implies_true] ) i ‹_›
        · exact hj

/-- If action a is applicable in bef, then after one h_1_step, all of a.add' are isSome. -/
lemma h_1_step_applicable_effects {n : ℕ} (prob : STRIPS n) (bef : Vector (WithTop ℕ) n)
    (a : Action n) (ha : a ∈ prob.actions')
    (happ : applicable' a (vec_to_state n bef) = true)
    (i : Fin n) (hi : i ∈ a.add'.val) :
    ((h_1_step n prob bef)[i]).isSome = true := by
  apply h_1_step_discovers prob bef i a ha hi
  intro j hj
  exact vec_to_state_isSome_of_applicable n bef a happ j hj

/-
The isSome pattern of h_1_step depends only on vec_to_state.
-/
lemma h_1_step_isSome_determined {n : ℕ} (prob : STRIPS n) (bef1 bef2 : Vector (WithTop ℕ) n)
    (heq : vec_to_state n bef1 = vec_to_state n bef2)
    (i : Fin n) :
    ((h_1_step n prob bef1)[i]).isSome = ((h_1_step n prob bef2)[i]).isSome := by
      have h_isSome_eq : ((h_1_step n prob bef1)[i]).isSome = true ↔ ((h_1_step n prob bef2)[i]).isSome = true := by
        by_cases h : ∃ a : Action n, a ∈ prob.actions' ∧ i ∈ a.add'.val ∧ applicable' a (vec_to_state n bef1) = true <;> simp_all +decide
        · obtain ⟨ a, ha, hi, ha' ⟩ := h; have := h_1_step_applicable_effects prob bef1 a; have := h_1_step_applicable_effects prob bef2 a; simp_all +decide
        · unfold h_1_step;
          rw [ Vector.getElem_map, Vector.getElem_map ];
          simp +zetaDelta at *;
          have := vec_to_state_getElem n bef1 i; have := vec_to_state_getElem n bef2 i;
          simp_all only [Fin.getElem_fin, Bool.false_eq_true, IsEmpty.forall_iff, implies_true,
      ↓reduceDIte]
      grind

/-- Once the isSome pattern stabilizes, it stays stable. -/
lemma h_1_step_stable_isSome {n : ℕ} (prob : STRIPS n) (bef : Vector (WithTop ℕ) n)
    (i : Fin n)
    (hstable : vec_to_state n (h_1_step n prob bef) = vec_to_state n bef) :
    ((h_1_step n prob (h_1_step n prob bef))[i]).isSome =
    ((h_1_step n prob bef)[i]).isSome := by
  exact h_1_step_isSome_determined prob (h_1_step n prob bef) bef hstable i

/-
If an applicable action's effect is NOT isSome in bef, then h_1_step discovers new facts.
-/
lemma h_1_step_changes_if_not_fixpoint {n : ℕ} (prob : STRIPS n) (bef : Vector (WithTop ℕ) n)
    (a : Action n) (ha : a ∈ prob.actions')
    (happ : applicable' a (vec_to_state n bef) = true)
    (i : Fin n) (hi : i ∈ a.add'.val) (hnot : (bef[i]).isSome = false) :
    vec_to_state n (h_1_step n prob bef) ≠ vec_to_state n bef := by
      have h_step_some : ((h_1_step n prob bef)[i]).isSome = true := by
        exact h_1_step_applicable_effects prob bef a ha happ i hi;
      intro H; have := vec_to_state_getElem n ( h_1_step n prob bef ) i; have := vec_to_state_getElem n bef i; aesop;

/-
If vec_to_state changes, then the applicable filter grows.
-/
lemma applicable_filter_grows {n : ℕ} (prob : STRIPS n)
    (bef_prev bef : Vector (WithTop ℕ) n)
    (hstep : bef = h_1_step n prob bef_prev)
    (hchanged : vec_to_state n (h_1_step n prob bef) ≠ vec_to_state n bef) :
    (prob.actions'.filter (fun a => applicable' a (vec_to_state n bef))).length >
    (prob.actions'.filter (fun a => applicable' a (vec_to_state n bef_prev))).length := by
      have h_filter_superset : ∀ a ∈ prob.actions', applicable' a (vec_to_state n bef_prev) → applicable' a (vec_to_state n bef) := by
        intros a ha happ
        have h_filter_superset : ∀ i ∈ a.pre'.val, (bef_prev[i]).isSome = true → (bef[i]).isSome = true := by
          intros i hi hprev
          rw [hstep]
          apply h_1_step_preserves_isSome
          exact hprev;
        unfold applicable' at *; simp_all
        unfold satisfies' at *; simp_all
        intro i hi; specialize h_filter_superset i hi; simp_all +decide [ vec_to_state_getElem ] ;
      -- Since there's at least one action applicable in bef but not in bef_prev, the filtered list for bef must have at least one more element than the filtered list for bef_prev.
      have h_filter_length : ∃ a ∈ prob.actions', applicable' a (vec_to_state n bef) ∧ ¬applicable' a (vec_to_state n bef_prev) := by
        contrapose! hchanged;
        have h_filter_eq : ∀ i : Fin n, (h_1_step n prob bef)[i].isSome = (bef)[i].isSome := by
          intro i
          by_cases h_add : ∃ a ∈ prob.actions', applicable' a (vec_to_state n bef) ∧ i ∈ a.add'.val;
          · obtain ⟨ a, ha₁, ha₂, ha₃ ⟩ := h_add;
            have h_filter_eq : (bef)[i].isSome = true := by
              have := h_1_step_applicable_effects prob bef_prev a ha₁ ( hchanged a ha₁ ha₂ ) i ha₃; aesop;
            rw [ h_1_step_preserves_isSome ] ; aesop ( simp_config := { singlePass := true } ) ;
            exact h_filter_eq
          · unfold h_1_step
            simp
            grind
        ext i;
        convert h_filter_eq ⟨ i, by assumption ⟩ using 1;
        · convert vec_to_state_getElem n ( h_1_step n prob bef ) ⟨ i, by assumption ⟩ using 1;
        · convert vec_to_state_getElem n bef ⟨ i, by assumption ⟩ using 1;
      have h_filter_length : List.Perm (List.filter (fun a => applicable' a (vec_to_state n bef)) prob.actions') (List.filter (fun a => applicable' a (vec_to_state n bef_prev)) prob.actions' ++ List.filter (fun a => applicable' a (vec_to_state n bef) ∧ ¬applicable' a (vec_to_state n bef_prev)) prob.actions') := by
        rw [ List.perm_iff_count ];
        intro a; by_cases ha : a ∈ prob.actions' <;> simp_all +decide [ List.count_eq_zero_of_not_mem ] ;
        grind +suggestions;
      have := h_filter_length.length_eq; simp_all +decide ;

/-- Iteration function for h_1_step. -/
def h_1_iter {n : ℕ} (prob : STRIPS n) (base : Vector (WithTop ℕ) n) : ℕ → Vector (WithTop ℕ) n
  | 0 => base
  | k + 1 => h_1_step n prob (h_1_iter prob base k)

/-- Shifting the base of iteration by one step. -/
lemma h_1_iter_shift {n : ℕ} (prob : STRIPS n) (base : Vector (WithTop ℕ) n) (k : ℕ) :
    h_1_iter prob (h_1_step n prob base) k = h_1_iter prob base (k + 1) := by
  induction k with
  | zero => simp [h_1_iter]
  | succ k ih => simp [h_1_iter, ih]

/-- foldl over a list of length k equals k iterations. -/
lemma h_1_foldl_eq_iter {n : ℕ} (prob : STRIPS n) (base : Vector (WithTop ℕ) n) (l : List α) :
    l.foldl (fun a _ => h_1_step n prob a) base = h_1_iter prob base l.length := by
  induction l generalizing base with
  | nil => simp [h_1_iter]
  | cons hd tl ih => simp [List.foldl]; rw [ih, h_1_iter_shift]

/-- If the isSome pattern is stable (vec_to_state unchanged by h_1_step),
    then the fixpoint property holds. -/
lemma stable_implies_fixpoint {n : ℕ} (prob : STRIPS n) (bef : Vector (WithTop ℕ) n)
    (hstable : vec_to_state n (h_1_step n prob bef) = vec_to_state n bef) :
    ∀ a ∈ prob.actions', applicable' a (vec_to_state n bef) = true →
      ∀ i ∈ a.add'.val, (bef[i]).isSome = true := by
  intro a ha happ i hi
  by_contra h
  simp at h
  exact absurd hstable (h_1_step_changes_if_not_fixpoint prob bef a ha happ i hi (by simp [h]))

/-
If the fixpoint property holds, then vec_to_state is stable.
-/
lemma fixpoint_implies_stable {n : ℕ} (prob : STRIPS n) (bef : Vector (WithTop ℕ) n)
    (hfix : ∀ a ∈ prob.actions', applicable' a (vec_to_state n bef) = true →
      ∀ i ∈ a.add'.val, (bef[i]).isSome = true) :
    vec_to_state n (h_1_step n prob bef) = vec_to_state n bef := by
      have h_vec_to_state_eq : ∀ i : Fin n, (vec_to_state n (h_1_step n prob bef))[i.val] = (vec_to_state n bef)[i.val] := by
        intro i; by_cases hi : ( bef[i] ).isSome = true <;> simp_all +decide [ vec_to_state_getElem ] ;
        · exact h_1_step_preserves_isSome prob bef i hi;
        · unfold h_1_step;
          simp +decide [ hi, updateIfCheaper ];
          grind;
      ext i;
      exact h_vec_to_state_eq ⟨ i, by assumption ⟩

/-
The fixpoint property is persistent: once achieved, it holds at all subsequent iterations.
-/
lemma fixpoint_persistent {n : ℕ} (prob : STRIPS n) (base : Vector (WithTop ℕ) n)
    (k : ℕ) (hfix : ∀ a ∈ prob.actions', applicable' a (vec_to_state n (h_1_iter prob base k)) = true →
      ∀ i ∈ a.add'.val, ((h_1_iter prob base k)[i]).isSome = true)
    (m : ℕ) (hm : m ≥ k) :
    ∀ a ∈ prob.actions', applicable' a (vec_to_state n (h_1_iter prob base m)) = true →
      ∀ i ∈ a.add'.val, ((h_1_iter prob base m)[i]).isSome = true := by
        induction' hm with m hm ih;
        · assumption;
        · intro a ha h;
          have h_eq : vec_to_state n (h_1_iter prob base (m + 1)) = vec_to_state n (h_1_iter prob base m) := by
            exact fixpoint_implies_stable prob _ ih;
          have h_eq : applicable' a (vec_to_state n (h_1_iter prob base m)) = true := by
            grind;
          exact fun i hi => h_1_step_preserves_isSome prob ( h_1_iter prob base m ) i ( ih a ha h_eq i hi )

--/-
--The number of non-fixpoint steps is bounded by the number of actions.
---/
--lemma h_1_fixpoint_step_bound {n : ℕ} (prob : STRIPS n) (v : State' n) :
--    ∃ k ≤ prob.actions'.length,
--      ∀ a ∈ prob.actions', applicable' a (vec_to_state n (h_1_iter prob (h_1_base n v) k)) = true →
--        ∀ i ∈ a.add'.val, ((h_1_iter prob (h_1_base n v) k)[i]).isSome = true := by
--          by_contra h;
--          -- By definition of `h_1_iter`, the number of steps is bounded by the length of the list of actions.
--          have h_bound : ∀ k ≤ prob.actions'.length, ¬ (∀ a ∈ prob.actions', applicable' a (vec_to_state n (h_1_iter prob (h_1_base n v) k)) = true → ∀ i ∈ a.add'.val, ((h_1_iter prob (h_1_base n v) k)[i]).isSome = true) := by
--            exact fun k hk => fun hk' => h ⟨ k, hk, hk' ⟩;
--          have h_bound : ∀ k ≤ prob.actions'.length, (prob.actions'.filter (fun a => applicable' a (vec_to_state n (h_1_iter prob (h_1_base n v) k)))).length > k := by
--            intro k hk
--            induction' k with k ih;
--            · simp +zetaDelta at *;
--              exact Exists.elim ( h_bound 0 bot_le ) fun x hx => ⟨ x, hx.1, hx.2.1 ⟩;
--            · have := applicable_filter_grows prob ( h_1_iter prob ( h_1_base n v ) k ) ( h_1_iter prob ( h_1_base n v ) ( k + 1 ) ) ?_ ?_;
--              · linarith [ ih ( Nat.le_of_succ_le hk ) ];
--              · grind +locals;
--              · exact fun h => h_bound ( k + 1 ) hk <| stable_implies_fixpoint prob _ h;
--          exact absurd ( h_bound _ le_rfl ) ( not_lt_of_ge ( List.length_filter_le _ _ ) )
--
--/-- After |actions| iterations, the fixpoint property holds. -/
--lemma h_1_foldl_is_fixpoint {n : ℕ} (prob : STRIPS n) (v : State' n) :
--    let result := (List.finRange prob.actions'.length).foldl
--      (fun a _ => h_1_step n prob a) (h_1_base n v)
--    ∀ a ∈ prob.actions', applicable' a (vec_to_state n result) = true →
--      ∀ i ∈ a.add'.val, (result[i]).isSome = true := by
--  intro result
--  have h_eq : result = h_1_iter prob (h_1_base n v) prob.actions'.length := by
--    simp [result, h_1_foldl_eq_iter, List.length_finRange]
--  rw [h_eq]
--  obtain ⟨k, hk, hfix⟩ := h_1_fixpoint_step_bound prob v
--  exact fixpoint_persistent prob (h_1_base n v) k hfix prob.actions'.length (by omega)
--
--/-- If a path exists, satisfies' holds after iterations. -/
--lemma h_1_satisfies_when_path_exists {n : ℕ} (prob : STRIPS n) (v : State' n)
--    (goal : State' n) (goal_in : goal ∈ trans_of_STRIPS_goals prob)
--    (path : WeightedDiGraph.Path (G := trans_of_STRIPS prob) v goal) :
--    let result := (List.finRange prob.actions'.length).foldl
--      (fun a _ => h_1_step n prob a) (h_1_base n v)
--    satisfies' prob.goal' (vec_to_state n result) = true := by
--  intro result
--  have hfix := h_1_foldl_is_fixpoint prob v
--  have hv : ∀ i : Fin n, v[i.val] = true → (result[i]).isSome = true :=
--    fun i hi => h_1_foldl_true_in_v_isSome prob v _ i hi
--  have goal_sat : satisfies' prob.goal' goal = true :=
--    (mem_trans_of_STRIPS_goals_iff prob goal).mp goal_in
--  unfold satisfies' at goal_sat ⊢
--  rw [List.all_eq_true] at goal_sat ⊢
--  intro i hi
--  have h_eq := vec_to_state_getElem n result i
--  change (vec_to_state n result)[i.val] = true
--  rw [h_eq]
--  exact walk_at_fixpoint_goal_isSome prob result hfix path.val hv i (goal_sat i hi)
--
--/-- After k iterations, foldl values are non-increasing (generalized base). -/
--lemma h_1_foldl_le_gen {n : ℕ} (prob : STRIPS n) (base : Vector (WithTop ℕ) n)
--    (l : List α) (i : Fin n) :
--    (l.foldl (fun a _ => h_1_step n prob a) base)[i] ≤ base[i] := by
--  induction l generalizing base with
--  | nil => simp
--  | cons hd tl ih =>
--    simp [List.foldl]
--    exact le_trans (ih (h_1_step n prob base)) (h_1_step_le n prob base i)
--
--/-
--After h_1_step, if bef[i] = some c then (h_1_step bef)[i] = some c' with c' ≤ c.
---/
--lemma h_1_step_val_le {n : ℕ} (prob : STRIPS n) (bef : Vector (WithTop ℕ) n) (i : Fin n)
--    (c : ℕ) (hc : bef[i] = some c) :
--    ∃ c' : ℕ, (h_1_step n prob bef)[i] = some c' ∧ c' ≤ c := by
--      by_contra! h_contra;
--      obtain ⟨c', hc'⟩ : ∃ c' : ℕ, (h_1_step n prob bef)[i] = some c' := by
--        cases h : ( h_1_step n prob bef )[i] <;> simp_all +decide;
--        · have := h_1_step_preserves_isSome prob bef i; simp_all +decide ;
--        · exact ⟨ _, rfl ⟩;
--      have h_le : (h_1_step n prob bef)[i] ≤ bef[i] := by
--        exact h_1_step_le n prob bef i;
--      exact not_le_of_gt ( h_contra c' hc' ) ( by rw [ hc' ] at h_le; rw [ hc ] at h_le; exact WithTop.coe_le_coe.mp h_le )
--
--/-
--After h_1_step, for facts in a.add' where a is applicable, the value is ≤ a.cost + B
--    where B bounds the precondition values.
---/
--lemma h_1_step_add_val_le {n : ℕ} (prob : STRIPS n) (bef : Vector (WithTop ℕ) n)
--    (a : Action n) (ha : a ∈ prob.actions')
--    (happ : applicable' a (vec_to_state n bef) = true)
--    (B : ℕ) (hB : ∀ j ∈ a.pre'.val, ∀ c : ℕ, bef[j] = some c → c ≤ B)
--    (i : Fin n) (hi : i ∈ a.add'.val) :
--    ∃ c : ℕ, (h_1_step n prob bef)[i] = some c ∧ c ≤ a.cost + B := by
--      have h_contribution : ∃ c, c ∈ (prob.actions'.filterMap (fun a =>
--        if i ∈ a.add'.1 then
--          if is_appli : applicable' a (vec_to_state n bef) then
--            let pre_cost : List ℕ := a.pre'.1.attach.map (fun x : { x : Fin n // x ∈ a.pre'.1 } =>
--              bef[x.1].get (by exact vec_to_state_isSome_of_applicable n bef a is_appli x.1 x.2))
--            if pre_cost_nil : pre_cost = [] then .some (a.cost) else .some (a.cost + pre_cost.max pre_cost_nil)
--          else .none
--        else .none)) ∧ c ≤ a.cost + B := by
--          refine' ⟨ _, _, _ ⟩;
--          exact if pre_cost_nil : ( a.pre'.1.attach.map ( fun x : { x : Fin n // x ∈ a.pre'.1 } => bef[x.1].get ( by exact vec_to_state_isSome_of_applicable n bef a happ x.1 x.2 ) ) ) = [] then a.cost else a.cost + ( a.pre'.1.attach.map ( fun x : { x : Fin n // x ∈ a.pre'.1 } => bef[x.1].get ( by exact vec_to_state_isSome_of_applicable n bef a happ x.1 x.2 ) ) ).max pre_cost_nil;
--          · grind +revert;
--          · split_ifs ; simp_all +decide [ List.max ];
--            refine' Nat.add_le_add_left _ _;
--            have h_max_le_B : ∀ x ∈ (a.pre'.1.attach.map (fun x : { x : Fin n // x ∈ a.pre'.1 } => bef[x.1].get (by exact vec_to_state_isSome_of_applicable n bef a happ x.1 x.2))), x ≤ B := by
--              aesop;
--            exact (List.max_le_iff ‹_›).mpr h_max_le_B;
--      unfold h_1_step;
--      unfold updateIfCheaper;
--      obtain ⟨ c, hc₁, hc₂ ⟩ := h_contribution;
--      have h_min_le : (List.filterMap (fun a =>
--        if i ∈ a.add'.1 then
--          if is_appli : applicable' a (vec_to_state n bef) then
--            let pre_cost : List ℕ := a.pre'.1.attach.map (fun x : { x : Fin n // x ∈ a.pre'.1 } =>
--              bef[x.1].get (by exact vec_to_state_isSome_of_applicable n bef a is_appli x.1 x.2))
--            if pre_cost_nil : pre_cost = [] then .some (a.cost) else .some (a.cost + pre_cost.max pre_cost_nil)
--          else .none
--        else .none) prob.actions').min (by
--        exact List.ne_nil_of_mem hc₁) ≤ some c := by
--          simp +zetaDelta at *;
--          convert List.min_le_of_mem _;
--          · infer_instance;
--          · infer_instance;
--          · grind;
--      grind
--
--/-
--After one h_1_step, all facts true in the successor state k (via action a from s→k)
--    have values bounded by B + edgeCost, where B bounds s's true fact values.
---/
--lemma h_1_step_successor_bound {n : ℕ} (prob : STRIPS n) (bef : Vector (WithTop ℕ) n)
--    (B : ℕ) {s k : State' n} (adj : (trans_of_STRIPS prob).Adj s k)
--    (hs_isSome : ∀ i : Fin n, s[i.val] = true → (bef[i]).isSome = true)
--    (hs_val : ∀ i : Fin n, s[i.val] = true → ∀ c : ℕ, bef[i] = some c → c ≤ B)
--    (j : Fin n) (hj : k[j.val] = true) :
--    ∃ c : ℕ, (h_1_step n prob bef)[j] = some c ∧ c ≤ B + NatGraph.edgeCost adj := by
--      -- By definition of `adj`, we know there exists an action `a` such that `applicable' a s` and `is_successor' a s k`.
--      obtain ⟨a, ha⟩ : ∃ a : Action n, a ∈ prob.actions' ∧ applicable' a s ∧ is_successor' a s k ∧ a.cost = NatGraph.edgeCost adj := by
--        have := min_cost_action_cost_eq_cost_of prob s k ( is_successor_state_of_trans_STRIPS_adj prob s k adj );
--        exact ⟨ _, min_cost_action_in_prob prob s k ( is_successor_state_of_trans_STRIPS_adj prob s k adj ), ( successor_implies_applicable ( min_cost_action_creates_successor prob s k adj ) ), ( successor_implies_is_successor ( min_cost_action_creates_successor prob s k adj ) ), this.trans ( by rw [ trans_of_STRIPS_edgeCost ] ) ⟩;
--      by_cases hj_add : j ∈ a.add'.1;
--      · obtain ⟨c, hc⟩ : ∃ c : ℕ, (h_1_step n prob bef)[j] = some c ∧ c ≤ a.cost + B := by
--          apply h_1_step_add_val_le;
--          · exact ha.1;
--          · unfold applicable' at *;
--            unfold satisfies' at *;
--            simp_all +decide [ vec_to_state_getElem ];
--          · intro i hi c hc; specialize hs_val i; simp_all +decide [ applicable' ] ;
--            unfold satisfies' at ha; aesop;
--          · exact hj_add;
--        grind;
--      · -- Since j is not in a.add', we have s[j] = true.
--        have hj_s : s[j.val] = true := by
--          have := List.all_eq_true.mp ha.2.2.1 j; aesop;
--        -- Since j is not in a.add', we have bef[j] = some c for some c.
--        obtain ⟨c, hc⟩ : ∃ c : ℕ, bef[j] = some c := by
--          exact Option.isSome_iff_exists.mp ( by simpa using hs_isSome j hj_s );
--        have := h_1_step_val_le prob bef j c hc;
--        exact ⟨ this.choose, this.choose_spec.1, le_trans this.choose_spec.2 ( le_trans ( hs_val j hj_s c hc ) ( Nat.le_add_right _ _ ) ) ⟩
--
--/-
--Walk-based value and isSome bound.
---/
--set_option maxHeartbeats 400000 in
--lemma h_1_walk_value_bound {n : ℕ} (prob : STRIPS n)
--    (bef : Vector (WithTop ℕ) n) (B : ℕ)
--    {s goal : State' n} (w : (trans_of_STRIPS prob).Walk s goal)
--    (hs_isSome : ∀ i : Fin n, s[i.val] = true → (bef[i]).isSome = true)
--    (hs_val : ∀ i : Fin n, s[i.val] = true → ∀ c : ℕ, bef[i] = some c → c ≤ B)
--    (l : List β) (hl : w.length ≤ l.length)
--    (j : Fin n) (hj : goal[j.val] = true) :
--    ∃ c : ℕ, (l.foldl (fun a _ => h_1_step n prob a) bef)[j] = some c ∧ c ≤ B + w.cost := by
--      by_contra h_contra;
--      induction' w with s goal w ih generalizing l bef B j;
--      · -- By definition of `h_1_foldl_le_gen`, we know that `(foldl l bef)[j] ≤ bef[j]`.
--        have h_foldl_le_bef : (List.foldl (fun a _ => h_1_step n prob a) bef l)[j] ≤ bef[j] := by
--          apply h_1_foldl_le_gen;
--        cases h : bef[j] <;> simp_all +decide;
--        · specialize hs_isSome j hj ; simp_all +decide;
--        · cases h' : ( List.foldl ( fun a x => h_1_step n prob a ) bef l )[ j ] <;> simp_all +decide;
--          exact not_le_of_gt ( h_contra _ rfl ) ( hs_val _ hj _ h |> le_trans h_foldl_le_bef );
--      · rcases l with ( _ | ⟨ x, l ⟩ ) <;> simp +decide [ WeightedDiGraph.Walk.length ] at hl ⊢;
--        rename_i h₁ h₂ h₃;
--        -- By definition of `h_1_step`, we know that `h_1_step n prob bef` satisfies the conditions for `w`.
--        obtain ⟨bef', B', hbef', hB'⟩ : ∃ bef' : Vector (WithTop ℕ) n, ∃ B' : ℕ, bef' = h_1_step n prob bef ∧ B' = B + NatGraph.edgeCost h₁ ∧ (∀ i : Fin n, w[i.val] = true → (bef'[i]).isSome = true) ∧ (∀ i : Fin n, w[i.val] = true → ∀ c : ℕ, bef'[i] = some c → c ≤ B') := by
--          refine' ⟨ _, _, rfl, rfl, _, _ ⟩;
--          · intro i hi
--            apply h_1_step_successor_bound prob bef B h₁ hs_isSome hs_val i hi |> fun ⟨c, hc⟩ => hc.1.symm ▸ by simp [hc.2];
--          · intro i hi c hc;
--            have := h_1_step_successor_bound prob bef B h₁ ( fun i hi => hs_isSome i hi ) ( fun i hi c hc => hs_val i hi c hc ) i hi;
--            grind +splitImp;
--        specialize h₃ bef' B' hB'.2.1 hB'.2.2 l ( by linarith ) j hj ; simp_all +decide [ WeightedDiGraph.Walk.cons ];
--        exact h_contra _ h₃.choose_spec.1 |> not_le_of_gt <| by linarith [ h₃.choose_spec.2, show ( WeightedDiGraph.Walk.cons h₁ h₂ ).cost = NatGraph.edgeCost h₁ + h₂.cost from rfl ] ;
--
--/-- Monotonicity: later iterations yield smaller or equal values. -/
--lemma iter_mono {n : ℕ} (prob : STRIPS n) (base : Vector (WithTop ℕ) n) (k : ℕ) (i : Fin n) :
--    (h_1_iter prob base (k + 1))[i] ≤ (h_1_iter prob base k)[i] := by
--  simp [h_1_iter]
--  exact h_1_step_le n prob _ i
--
--/-- For l₁ ≤ l₂, (iter l₂)[i] ≤ (iter l₁)[i]. -/
--lemma iter_antitone {n : ℕ} (prob : STRIPS n) (base : Vector (WithTop ℕ) n)
--    (l₁ l₂ : ℕ) (h : l₁ ≤ l₂) (i : Fin n) :
--    (h_1_iter prob base l₂)[i] ≤ (h_1_iter prob base l₁)[i] := by
--  induction h with
--  | refl => rfl
--  | step h ih => exact le_trans (iter_mono prob base _ i) ih
--
--/-- Squeezing: if the value at step k equals the value at step m, then
--    it equals the value at all intermediate steps. -/
--lemma iter_squeezed {n : ℕ} (prob : STRIPS n) (base : Vector (WithTop ℕ) n)
--    {k l m : ℕ} (hkl : k ≤ l) (hlm : l ≤ m) (i : Fin n)
--    (hk : (h_1_iter prob base k)[i] = (h_1_iter prob base m)[i]) :
--    (h_1_iter prob base l)[i] = (h_1_iter prob base m)[i] :=
--  le_antisymm (hk ▸ iter_antitone prob base k l hkl i) (iter_antitone prob base l m hlm i)
--
--/-- At any step between k and m where the value equals the final value,
--    the value stays equal to the final value. -/
--lemma iter_stable_from_first {n : ℕ} (prob : STRIPS n) (base : Vector (WithTop ℕ) n)
--    (m : ℕ) (i : Fin n) (c : ℕ)
--    (hm : (h_1_iter prob base m)[i] = some c)
--    (l : ℕ) (hl : l ≤ m)
--    (hlc : (h_1_iter prob base l)[i] = some c) :
--    ∀ l' : ℕ, l ≤ l' → l' ≤ m → (h_1_iter prob base l')[i] = some c := by
--  intro l' hll' hl'm
--  have := iter_squeezed prob base hll' hl'm i (hlc.trans hm.symm)
--  rw [hm] at this
--  exact this
--
--/-- updateIfCheaper preserves the value when newCost ≥ current value. -/
--lemma updateIfCheaper_ge_no_change (c v : ℕ) (hge : c ≥ v) :
--    updateIfCheaper c (some v) = some v := by
--  unfold updateIfCheaper
--  simp [not_lt.mpr hge]
--
--/-
--At the fixpoint, none values are preserved by h_1_step.
---/
--lemma h_1_value_fixpoint_none {n : ℕ} (prob : STRIPS n) (v : State' n) (i : Fin n)
--    (h : (h_1_iter prob (h_1_base n v) prob.actions'.length)[i] = none) :
--    (h_1_step n prob (h_1_iter prob (h_1_base n v) prob.actions'.length))[i] = none := by
--  contrapose! h;
--  obtain ⟨c, hc⟩ : ∃ c : ℕ, (h_1_step n prob (h_1_iter prob (h_1_base n v) (List.length prob.actions')))[i] = some c := by
--    exact Option.ne_none_iff_exists'.mp h;
--  have h_fixpoint : vec_to_state n (h_1_step n prob (h_1_iter prob (h_1_base n v) (List.length prob.actions'))) = vec_to_state n (h_1_iter prob (h_1_base n v) (List.length prob.actions')) := by
--    apply fixpoint_implies_stable;
--    convert h_1_foldl_is_fixpoint prob v using 1;
--    rw [ h_1_foldl_eq_iter ];
--    rw [ List.length_finRange ];
--  replace h_fixpoint := congr_arg ( fun x => x[i.val] ) h_fixpoint ; simp_all +decide [ vec_to_state_getElem ];
--  grind
--
--/-- At the fixpoint, some values are preserved by h_1_step.
--    Proof by strong induction on c. For c = 0, trivial since costs ≥ 0.
--    For c > 0, by IH all preconditions with value < c are fixpoints.
--    At step m, the minimum cost was ≥ c (since the value stayed at c).
--    At step m+1, using R values: costs with max precondition ≥ c are trivially ≥ c.
--    Costs with all preconditions < c use fixpoint values, giving the same costs as step m. -/
--lemma h_1_value_fixpoint_some {n : ℕ} (prob : STRIPS n) (v : State' n) (i : Fin n) (c : ℕ)
--    (h : (h_1_iter prob (h_1_base n v) prob.actions'.length)[i] = some c) :
--    (h_1_step n prob (h_1_iter prob (h_1_base n v) prob.actions'.length))[i] = some c := by
--  set m := prob.actions'.length with hm_def
--  set R := h_1_iter prob (h_1_base n v) m with hR_def
--  obtain ⟨c', hc', hle⟩ := h_1_step_val_le prob R i c h
--  suffices h_ge : c ≤ c' by
--    rw [show c' = c from Nat.le_antisymm hle h_ge] at hc'; exact hc'
--  -- From h_1_step_le: c' ≤ c. Need c ≤ c'.
--  -- For c = 0: trivial
--  match c, h with
--  | 0, h => exact Nat.zero_le c'
--  | c + 1, h =>
--    -- For c > 0: need c+1 ≤ c'
--    -- By contradiction: assume c' < c+1, i.e., c' ≤ c
--    by_contra h_contra
--    push_neg at h_contra
--    -- c' < c + 1, i.e., c' ≤ c. Combined with hle (c' ≤ c+1-1 = c): c' ≤ c.
--    -- And c' < c + 1 means c' ≤ c.
--    -- So (h_1_step R)[i] = some c' with c' < c + 1.
--    -- This means updateIfCheaper produced a STRICTLY smaller value.
--    -- At step m+1, the minimum cost was c' < c+1.
--    -- But at step m, the value was c+1. Since (iter l)[i] = some (c+1)
--    -- for k_i ≤ l ≤ m (squeezing), the minimum cost at every step
--    -- from k_i+1 to m was ≥ c+1.
--    -- The contradiction comes from the fact that precondition values
--    -- at step m+1 (= R values) would have to be strictly lower than
--    -- at step m (= iter(m-1) values) for the cost to drop below c+1.
--    ...
--
--/-- After the fixpoint, h_1_step is idempotent on values. -/
--lemma h_1_value_fixpoint {n : ℕ} (prob : STRIPS n) (v : State' n) :
--    h_1_step n prob (h_1_iter prob (h_1_base n v) prob.actions'.length) =
--    h_1_iter prob (h_1_base n v) prob.actions'.length := by
--  ext i
--  cases h : (h_1_iter prob (h_1_base n v) prob.actions'.length)[i] with
--  | top => exact h_1_value_fixpoint_none prob v ⟨i, ‹_›⟩ h
--  | coe c => exact h_1_value_fixpoint_some prob v ⟨i, ‹_›⟩ c h
--
--/-- After prob.actions'.length iterations, additional iterations don't change the result. -/
--lemma h_1_iter_stable {n : ℕ} (prob : STRIPS n) (v : State' n) (k : ℕ) :
--    h_1_iter prob (h_1_base n v) (prob.actions'.length + k) =
--    h_1_iter prob (h_1_base n v) prob.actions'.length := by
--  induction k with
--  | zero => simp
--  | succ k ih =>
--    show h_1_step n prob (h_1_iter prob (h_1_base n v) (prob.actions'.length + k)) = _
--    rw [ih]
--    exact h_1_value_fixpoint prob v
--
--/-- foldl over a longer list gives the same result as over finRange prob.actions'.length. -/
--lemma h_1_foldl_stable_ext {n : ℕ} (prob : STRIPS n) (v : State' n)
--    (l : List β) (hl : l.length ≥ prob.actions'.length) :
--    l.foldl (fun a _ => h_1_step n prob a) (h_1_base n v) =
--    (List.finRange prob.actions'.length).foldl (fun a _ => h_1_step n prob a) (h_1_base n v) := by
--  rw [h_1_foldl_eq_iter, h_1_foldl_eq_iter]
--  simp [List.length_finRange]
--  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hl
--  rw [hd, h_1_iter_stable]
--
--/-- For each goal fact i, the computed result value is ≤ any path cost from v to any goal. -/
--lemma h_1_goal_value_le_path_cost {n : ℕ} (prob : STRIPS n) (v : State' n)
--    (i : Fin n) (hi : i ∈ prob.goal'.val) (c : ℕ)
--    (h_val : ((List.finRange prob.actions'.length).foldl
--      (fun a _ => h_1_step n prob a) (h_1_base n v))[i] = some c)
--    (goal : State' n) (goal_in : goal ∈ trans_of_STRIPS_goals prob)
--    (path : WeightedDiGraph.Path (G := trans_of_STRIPS prob) v goal) :
--    c ≤ path.cost := by
--  -- Use h_1_walk_value_bound with a list long enough for the walk
--  set M := max prob.actions'.length path.val.length with hM_def
--  have hM_ge_actions : M ≥ prob.actions'.length := le_max_left _ _
--  have hM_ge_walk : path.val.length ≤ M := le_max_right _ _
--  -- Create a list of length M
--  set l := List.finRange M with hl_def
--  have hl_len : l.length = M := List.length_finRange
--  -- The foldl over l gives the same as over finRange prob.actions'.length
--  have h_eq : l.foldl (fun a _ => h_1_step n prob a) (h_1_base n v) =
--    (List.finRange prob.actions'.length).foldl (fun a _ => h_1_step n prob a) (h_1_base n v) :=
--    h_1_foldl_stable_ext prob v l (by omega)
--  -- Get the bound from h_1_walk_value_bound
--  have goal_sat : satisfies' prob.goal' goal = true :=
--    (mem_trans_of_STRIPS_goals_iff prob goal).mp goal_in
--  have hj : goal[i.val] = true := by
--    unfold satisfies' at goal_sat; rw [List.all_eq_true] at goal_sat; exact goal_sat i hi
--  have h_base_isSome : ∀ j : Fin n, v[j.val] = true → ((h_1_base n v)[j]).isSome = true := by
--    intro j hj; unfold h_1_base; simp [hj]
--  have h_base_val : ∀ j : Fin n, v[j.val] = true → ∀ c : ℕ, (h_1_base n v)[j] = some c → c ≤ 0 := by
--    intro j hj c hc; unfold h_1_base at hc; simp [hj] at hc; cases hc; rfl
--  obtain ⟨c', hc'_eq, hc'_le⟩ := h_1_walk_value_bound prob (h_1_base n v) 0 path.val
--    h_base_isSome h_base_val l (by rw [hl_len]; exact hM_ge_walk) i hj
--  -- The value from the extended list equals the value from the original list
--  rw [h_eq] at hc'_eq
--  -- So c' = c
--  rw [h_val] at hc'_eq
--  cases hc'_eq
--  -- c ≤ 0 + path.val.cost = path.cost
--  simp at hc'_le
--  rw [WeightedDiGraph.Path.cost_same]
--  exact hc'_le
--
--lemma h_1_admissible {n : ℕ} (prob : STRIPS n) : heur_admissible' prob (h_1 prob) := by
--  intro v goal goal_in path;
--  unfold h_1;
--  by_cases h : satisfies' prob.goal' ( vec_to_state n ( List.foldl ( fun a _ => h_1_step n prob a ) ( h_1_base n v ) ( List.finRange ( List.length prob.actions' ) ) ) ) <;> simp_all +decide;
--  · split_ifs <;> simp_all +decide [ List.max ];
--    have h_max_le : ∀ x ∈ (prob.goal'.val.attach.map (fun x : { x : Fin n // x ∈ prob.goal'.val } => (List.foldl (fun a x => h_1_step n prob a) (h_1_base n v) (List.finRange (List.length prob.actions')))[x.1].get (by exact vec_to_state_isSome_of_satisfies n (List.foldl (fun a x => h_1_step n prob a) (h_1_base n v) (List.finRange (List.length prob.actions'))) prob.goal' ‹_› x.1 x.2))), x ≤ path.cost := by
--      simp +zetaDelta at *;
--      intro x i hi hx; have := h_1_goal_value_le_path_cost prob v i hi x ( by aesop ) goal goal_in path; aesop;
--    convert h_max_le _ _;
--    convert List.max_mem _;
--    exact Nat.instLawfulOrderMax.toMaxEqOr;
--  · exact absurd h ( by have := h_1_satisfies_when_path_exists prob v goal goal_in path; aesop )

end Validator
