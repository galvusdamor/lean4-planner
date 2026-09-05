import planning.H1

/-!
# A faster implementation of the `h_1` heuristic

`STRIPS.h_1` (see `planning.CriticalPath` and `planning.H1`) is defined as the fixpoint of
`h_1_step`, and `h_1_step` recomputes, for **every** variable `i` and **every** action `a`,
the lists `a.pre.toList` and `a.add.toList` and the test `i ∈ a.add.toList`.  Since
`VarSet.toList` filters the list of *all* `n` variables, one sweep of `h_1_step` costs
`O(n² · |A|)` — for a task with a few hundred variables and a few thousand actions that is
tens of millions of operations *per sweep*, and the fixpoint needs one sweep per level.

This module defines `STRIPS.h_1_fast`, which computes the same values in `O(Σ_a (|pre a| +
|add a|))` per sweep:

* the precondition and add lists of the actions, and their costs, are extracted **once** per
  task (`STRIPS.h1Data`), not once per variable, per action and per sweep;
* a sweep iterates over the actions (not over the variable/action pairs): for an applicable
  action it computes its contribution once and relaxes the entries of its add list;
* applicability is read off the value vector directly (an action is applicable in
  `vec_to_state n bef` iff all its preconditions have a finite value in `bef`), so no state
  bit vector is built.

The main result is `STRIPS.h_1_fast_eq : h_1_fast prob s = h_1 prob s`, so `h_1_fast` is the
same heuristic — in particular it is admissible, goal aware and consistent by the theorems of
`planning.H1`; `STRIPS.h_1_fast_admissible` states admissibility explicitly.

The original definitions are unchanged.
-/

namespace STRIPS

variable {n : ℕ}

/-! ### Pre-extracted action data -/

/-- The data of one action that a sweep of the `h_1` fixpoint needs: its precondition list,
its add list and its cost. -/
structure H1Action (n : ℕ) where
  /-- The preconditions of the action, enumerated. -/
  pre : List (Fin n)
  /-- The add effects of the action, enumerated. -/
  add : List (Fin n)
  /-- The cost of the action. -/
  cost : ℕ

/-- The action data of a planning task, extracted once. -/
def h1Data (prob : PlanningTask n) : List (H1Action n) :=
  prob.actions'.map (fun a => ⟨a.pre.toList, a.add.toList, a.cost⟩)

/-! ### One sweep -/

/-- The contribution of an action to the value of the facts it adds: `none` if one of its
preconditions is still unreached (which is exactly the case in which the action is not
applicable in `vec_to_state n bef`), otherwise the maximum of the values of its
preconditions, accumulated in `acc`. -/
def h1PreMax (bef : Vector (WithTop ℕ) n) : List (Fin n) → ℕ → Option ℕ
  | [], acc => some acc
  | x :: xs, acc =>
      if (bef[x]).isSome then h1PreMax bef xs (max acc ((bef[x]).getD 0)) else none

/-- Relax the entries of `l` in `out` with the new value `c`. -/
def h1Relax (c : ℕ) : List (Fin n) → Vector (WithTop ℕ) n → Vector (WithTop ℕ) n
  | [], out => out
  | x :: xs, out => h1Relax c xs (out.set x.1 (updateIfCheaper c out[x]) x.2)

/-- The relaxation contributed by one action in a sweep: nothing if the action is not
applicable, otherwise its add effects are relaxed with its contribution. -/
def h1RelaxAction (bef : Vector (WithTop ℕ) n) (d : H1Action n) (out : Vector (WithTop ℕ) n) :
    Vector (WithTop ℕ) n :=
  match h1PreMax bef d.pre 0 with
  | none => out
  | some m => h1Relax (d.cost + m) d.add out

/-- One sweep of the `h_1` fixpoint iteration, over the pre-extracted action data. -/
def h1StepFast (data : List (H1Action n)) (bef : Vector (WithTop ℕ) n) :
    Vector (WithTop ℕ) n :=
  data.foldl (fun out d => h1RelaxAction bef d out) bef

/-! ### The relaxation of one entry -/

/-- `updateIfCheaper` is the minimum. -/
lemma updateIfCheaper_eq_min (c : ℕ) (v : WithTop ℕ) :
    updateIfCheaper c v = min (c : WithTop ℕ) v := by
  cases v with
  | top => simp [updateIfCheaper]; rfl
  | coe x =>
    by_cases h : c < x
    · have h1 : updateIfCheaper c (x : WithTop ℕ) = (c : WithTop ℕ) := by
        simp [updateIfCheaper, h]; rfl
      exact h1.trans (min_eq_left (WithTop.coe_le_coe.mpr h.le)).symm
    · have h1 : updateIfCheaper c (x : WithTop ℕ) = (x : WithTop ℕ) := by
        simp [updateIfCheaper, h]
      exact h1.trans (min_eq_right (WithTop.coe_le_coe.mpr (Nat.le_of_not_lt h))).symm

/-- The minimum of two coerced naturals is the coercion of their minimum. -/
lemma coe_min_withTop (a b : ℕ) :
    min (a : WithTop ℕ) (b : WithTop ℕ) = ((min a b : ℕ) : WithTop ℕ) := by
  rcases le_total a b with h | h
  · rw [Nat.min_def, if_pos h]
    exact min_eq_left (WithTop.coe_le_coe.mpr h)
  · rw [Nat.min_def]
    split_ifs with h2
    · exact min_eq_left (WithTop.coe_le_coe.mpr h2)
    · exact min_eq_right (WithTop.coe_le_coe.mpr h)

/-- Relaxing twice with the same value is relaxing once. -/
lemma updateIfCheaper_idem (c : ℕ) (v : WithTop ℕ) :
    updateIfCheaper c (updateIfCheaper c v) = updateIfCheaper c v := by
  cases v with
  | top => simp [updateIfCheaper]
  | coe x => simp only [updateIfCheaper]; split_ifs with h1 <;> simp_all

/-- Relaxing one entry with a list of candidate values. -/
def relaxFold (cs : List ℕ) (v : WithTop ℕ) : WithTop ℕ :=
  cs.foldl (fun v c => updateIfCheaper c v) v

@[simp] lemma relaxFold_nil (v : WithTop ℕ) : relaxFold [] v = v := rfl

@[simp] lemma relaxFold_cons (c : ℕ) (cs : List ℕ) (v : WithTop ℕ) :
    relaxFold (c :: cs) v = relaxFold cs (updateIfCheaper c v) := rfl

lemma relaxFold_append (cs ds : List ℕ) (v : WithTop ℕ) :
    relaxFold (cs ++ ds) v = relaxFold ds (relaxFold cs v) := by
  simp [relaxFold, List.foldl_append]

private lemma relaxFold_foldl_min (cs : List ℕ) (a : ℕ) (v : WithTop ℕ) :
    relaxFold cs (min (a : WithTop ℕ) v) = min ((cs.foldl min a : ℕ) : WithTop ℕ) v := by
  induction cs generalizing a v with
  | nil => simp
  | cons c cs ih =>
    rw [relaxFold_cons, updateIfCheaper_eq_min, ← min_assoc, min_comm (c : WithTop ℕ),
      coe_min_withTop, ih]
    simp [List.foldl_cons]

/-- `relaxFold` takes the minimum of the entry and all candidates. -/
lemma relaxFold_eq (cs : List ℕ) (v : WithTop ℕ) :
    relaxFold cs v = if h : cs = [] then v else updateIfCheaper (cs.min h) v := by
  cases cs with
  | nil => simp
  | cons c cs =>
    rw [dif_neg (by simp), relaxFold_cons, updateIfCheaper_eq_min, relaxFold_foldl_min,
      updateIfCheaper_eq_min]
    rfl

/-! ### The sweep is `h_1_step` -/

/-- Reading an entry after a relaxation pass. -/
lemma h1Relax_getElem (c : ℕ) (l : List (Fin n)) (out : Vector (WithTop ℕ) n) (i : Fin n) :
    (h1Relax c l out)[i] = if i ∈ l then updateIfCheaper c out[i] else out[i] := by
  induction l generalizing out with
  | nil => simp [h1Relax]
  | cons x xs ih =>
    rw [h1Relax, ih]
    by_cases hx : i = x
    · subst hx
      by_cases hmem : i ∈ xs
      · simp only [hmem, List.mem_cons, true_or, if_pos, Fin.getElem_fin,
          Vector.getElem_set_self]
        exact updateIfCheaper_idem _ _
      · simp [hmem, Vector.getElem_set_self]
    · have hne : (x : ℕ) ≠ (i : ℕ) := fun h => hx (Fin.ext h).symm
      by_cases hmem : i ∈ xs <;>
        simp [hmem, hx, Vector.getElem_set_ne _ _ hne]

/-- `h1PreMax` computes the maximum of the precondition values, and fails exactly when one of
them is unreached. -/
lemma h1PreMax_eq (bef : Vector (WithTop ℕ) n) (l : List (Fin n)) (acc : ℕ) :
    h1PreMax bef l acc =
      if ∀ x ∈ l, (bef[x]).isSome then
        some (l.foldl (fun acc x => max acc ((bef[x]).getD 0)) acc)
      else none := by
  induction l generalizing acc with
  | nil => simp [h1PreMax]
  | cons x xs ih =>
    rw [h1PreMax]
    by_cases hs : (bef[x]).isSome
    · rw [if_pos hs, ih]
      simp only [List.forall_mem_cons, hs, true_and, List.foldl_cons]
    · rw [if_neg hs, if_neg (fun hall => hs (hall x (List.mem_cons_self ..)))]

/-- An action is applicable in `vec_to_state n bef` exactly when all its preconditions have a
finite value in `bef`. -/
lemma applicable_iff_pre_isSome (bef : Vector (WithTop ℕ) n) (a : Action n) :
    applicable' a (vec_to_state n bef) = true ↔ ∀ x ∈ a.pre.toList, (bef[x]).isSome := by
  constructor
  · intro h x hx
    exact vec_to_state_isSome_of_applicable n bef a h x hx
  · intro h
    unfold applicable' satisfies'
    apply decide_eq_true
    intro i hi
    rw [vec_to_state_getElem]
    exact h i (by unfold VarSet.toList; exact hi)

/-- The contribution computed by the fast sweep is `actionContribUB`. -/
lemma h1PreMax_contrib (bef : Vector (WithTop ℕ) n) (a : Action n) (m : ℕ)
    (h : h1PreMax bef a.pre.toList 0 = some m) : a.cost + m = actionContribUB bef a := by
  rw [h1PreMax_eq] at h
  split_ifs at h with hall
  rw [Option.some.injEq] at h
  subst h
  rw [actionContribUB, List.foldl_map]

/-- The candidate values that one action contributes to the entry `i`. -/
def h1Contribs (bef : Vector (WithTop ℕ) n) (i : Fin n) (d : H1Action n) : List ℕ :=
  (h1PreMax bef d.pre 0).elim [] (fun m => if i ∈ d.add then [d.cost + m] else [])

/-- Reading an entry after the relaxation of one action. -/
lemma h1RelaxAction_getElem (bef : Vector (WithTop ℕ) n) (d : H1Action n)
    (out : Vector (WithTop ℕ) n) (i : Fin n) :
    (h1RelaxAction bef d out)[i] = relaxFold (h1Contribs bef i d) out[i] := by
  unfold h1RelaxAction h1Contribs
  cases h : h1PreMax bef d.pre 0 with
  | none => simp
  | some m =>
    rw [h1Relax_getElem]
    by_cases hmem : i ∈ d.add <;> simp [hmem, relaxFold]

/-- The per-index value of a fast sweep over an arbitrary action list. -/
lemma h1StepFast_foldl_getElem (bef : Vector (WithTop ℕ) n) (D : List (H1Action n))
    (out : Vector (WithTop ℕ) n) (i : Fin n) :
    (D.foldl (fun out d => h1RelaxAction bef d out) out)[i]
      = relaxFold (D.flatMap (h1Contribs bef i)) out[i] := by
  induction D generalizing out with
  | nil => simp [relaxFold]
  | cons d D ih =>
    rw [List.foldl_cons, ih, List.flatMap_cons, relaxFold_append, h1RelaxAction_getElem]

/-- The candidate values of the extracted action data are the ones `h_1_step` uses. -/
lemma flatMap_h1Contribs_eq (bef : Vector (WithTop ℕ) n) (i : Fin n) (L : List (Action n)) :
    (L.map (fun a => (⟨a.pre.toList, a.add.toList, a.cost⟩ : H1Action n))).flatMap
        (h1Contribs bef i)
      = L.filterMap (fun a =>
          if i ∈ a.add.toList then
            if applicable' a (vec_to_state n bef) then some (actionContribUB bef a) else none
          else none) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.map_cons, List.flatMap_cons, List.filterMap_cons, ih]
    by_cases happ : applicable' a (vec_to_state n bef) = true
    · obtain ⟨m, hpm⟩ : ∃ m, h1PreMax bef a.pre.toList 0 = some m := by
        rw [h1PreMax_eq, if_pos ((applicable_iff_pre_isSome bef a).1 happ)]
        exact ⟨_, rfl⟩
      have hc : a.cost + m = actionContribUB bef a := h1PreMax_contrib bef a m hpm
      by_cases hmem : i ∈ a.add.toList
      · simp [h1Contribs, hpm, hmem, happ, hc]
      · simp [h1Contribs, hpm, hmem]
    · have hpm : h1PreMax bef a.pre.toList 0 = none := by
        rw [h1PreMax_eq, if_neg (fun hall => happ ((applicable_iff_pre_isSome bef a).2 hall))]
      simp [h1Contribs, hpm, happ]

/-- The fast sweep computes the same vector as `h_1_step`. -/
theorem h1StepFast_eq (prob : PlanningTask n) (bef : Vector (WithTop ℕ) n) :
    h1StepFast (h1Data prob) bef = h_1_step n prob bef := by
  apply Vector.ext
  intro i hi
  rw [show (h_1_step n prob bef)[i] = (h_1_step n prob bef)[(⟨i, hi⟩ : Fin n)] from rfl,
    h_1_step_getElem_contrib]
  show (h1StepFast (h1Data prob) bef)[(⟨i, hi⟩ : Fin n)] = _
  rw [h1StepFast, h1Data, h1StepFast_foldl_getElem, flatMap_h1Contribs_eq, relaxFold_eq]

/-! ### The fixpoint -/

/-- The fixpoint of the fast sweep.  The data is carried together with the proof that it is
the data of `prob`, which is what makes the recursion terminate (the sweep is then the
original `h_1_step`, which decreases the value vector lexicographically). -/
def h1IterFixFast (prob : PlanningTask n) (data : List (H1Action n))
    (hdata : data = h1Data prob) (bef : Vector (WithTop ℕ) n) : Vector (WithTop ℕ) n :=
  let next := h1StepFast data bef
  if _h : next = bef then bef
  else h1IterFixFast prob data hdata next
termination_by bef
decreasing_by
  subst hdata
  rw [h1StepFast_eq]
  refine h_1_step_lex_decreasing prob bef ?_
  rw [← h1StepFast_eq prob bef]
  exact _h

/-- The fast fixpoint is the fixpoint of `h_1_step`. -/
theorem h1IterFixFast_eq_self (prob : PlanningTask n) (bef : Vector (WithTop ℕ) n) :
    h1IterFixFast prob (h1Data prob) rfl bef = h_1_iter_fix n prob bef := by
  rw [h1IterFixFast, h_1_iter_fix]
  by_cases h : h_1_step n prob bef = bef
  · rw [dif_pos (by rw [h1StepFast_eq]; exact h), dif_pos h]
  · rw [dif_neg (by rw [h1StepFast_eq]; exact h), dif_neg h, h1StepFast_eq]
    exact h1IterFixFast_eq_self prob (h_1_step n prob bef)
termination_by bef
decreasing_by exact h_1_step_lex_decreasing prob bef ‹_›

/-- The fast fixpoint is the fixpoint of `h_1_step`. -/
theorem h1IterFixFast_eq (prob : PlanningTask n) (data : List (H1Action n))
    (hdata : data = h1Data prob) (bef : Vector (WithTop ℕ) n) :
    h1IterFixFast prob data hdata bef = h_1_iter_fix n prob bef := by
  subst hdata
  exact h1IterFixFast_eq_self prob bef

/-! ### The heuristic -/

/-- **The fast `h_1` heuristic.**  The action data and the goal list are extracted once, when
the heuristic is created; evaluating it on a state then only runs the fixpoint iteration.
Proved equal to `h_1` in `h_1_fast_eq`. -/
def h_1_fast (prob : PlanningTask n) : BitVec n → ℕ :=
  let d : {d : List (H1Action n) // d = h1Data prob} := ⟨h1Data prob, rfl⟩
  let goal : List (Fin n) := prob.goal'.toList
  fun s =>
    let result := h1IterFixFast prob d.1 d.2 (h_1_base n s)
    if satisfies' prob.goal' (vec_to_state n result) then
      goal.map (fun i => result[i].getD 0) |>.foldl max 0
    else
      Vector.maxFinite result + 1

/-- **`h_1_fast` is `h_1`.** -/
theorem h_1_fast_eq (prob : PlanningTask n) (s : BitVec n) : h_1_fast prob s = h_1 prob s := by
  show (if satisfies' prob.goal' (vec_to_state n (h1IterFixFast prob (h1Data prob) rfl
      (h_1_base n s))) then _ else _) = _
  rw [h1IterFixFast_eq]
  rfl

/-- `h_1_fast` is admissible (it is `h_1`). -/
theorem h_1_fast_admissible (prob : PlanningTask n) :
    heur_admissible prob (fun s => (h_1_fast prob s : ℕ∞)) := by
  have : (fun s => ((h_1_fast prob s : ℕ) : ℕ∞)) = (fun s => ((h_1 prob s : ℕ) : ℕ∞)) := by
    funext s; rw [h_1_fast_eq]
  rw [this]
  exact h_1_admissible prob

end STRIPS
