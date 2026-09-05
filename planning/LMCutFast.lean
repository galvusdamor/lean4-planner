import planning.LMCutH1PCF
import planning.H1Fast

/-!
# A faster implementation of the LM-cut heuristic

`STRIPS.lmcut prob s STRIPS.h1_pcf` (see `planning.LMCutHeuristic`, `planning.LandmarkCutting`
and `planning.LMCutH1PCF`) is defined in a way that is convenient for the correctness proofs
but extremely expensive to run:

* the precondition-choice function `STRIPS.h1_pcf` computes, for **every** precondition of
  **every** action, a complete `h_1` fixpoint of the whole task (`h1_goal_value`);
* the justification graph re-evaluates the precondition-choice function inside every
  adjacency query and every payload computation;
* the goal zone is computed by running A\* once from every fact.

This module builds an implementation that computes the *same value* and reuses each of these
computations.  The pieces are:

* `STRIPS.h1Values` — the `h^max` value of every fact, read off a single `h_1` fixpoint
  vector, with `STRIPS.h1Values_eq` identifying it with `h1_goal_value`;
* `STRIPS.h1_pcf_fast` — the maximiser precondition-choice function computed from
  `h1Values`, with `STRIPS.h1_pcf_fast_eq : h1_pcf_fast = h1_pcf`;
* `STRIPS.lmcut_fast` — the LM-cut heuristic run with it, with
  `STRIPS.lmcut_fast_eq : lmcut_fast prob s = lmcut prob s h1_pcf`.

The original definitions are unchanged.
-/

namespace STRIPS

variable {n : ℕ}

/-! ### All `h_1` values from one fixpoint -/

/-- The `h^max` values of *all* facts of `p`, read off a single `h_1` fixpoint vector: a fact
that the fixpoint does not reach gets the same "unreachable" value as `h_1` gives it, namely
one more than the largest finite entry of the fixpoint. -/
def h1Values (p : PlanningTask n) : Vector ℕ n :=
  let v := h1IterFixFast p (h1Data p) rfl (h_1_base n p.init'.toBitVec)
  let unreach := Vector.maxFinite v + 1
  v.map (fun x => x.getD unreach)

/-- `h1Values` is `h1_goal_value`. -/
theorem h1Values_eq (p : PlanningTask n) (f : Fin n) :
    (h1Values p)[f] = h1_goal_value p f := by
  have hget : (h1Values p)[f]
      = ((h_1_iter_fix n p (h_1_base n p.init'.toBitVec))[f]).getD
          (Vector.maxFinite (h_1_iter_fix n p (h_1_base n p.init'.toBitVec)) + 1) := by
    simp [h1Values, h1IterFixFast_eq_self]
  rw [hget]
  by_cases hs : ((h_1_iter_fix n p (h_1_base n p.init'.toBitVec))[f]).isSome
  · obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hs
    rw [h1_goal_value, h_1_singleton_eq_getD p f p.init'.toBitVec hs, hc]
    simp
  · have hnone : (h_1_iter_fix n p (h_1_base n p.init'.toBitVec))[f] = none :=
      Option.not_isSome_iff_eq_none.mp hs
    have hnsat : ¬ satisfies' (singletonVarSet f)
        (vec_to_state n (h_1_iter_fix n p (h_1_base n p.init'.toBitVec))) = true := by
      rw [satisfies'_singleton, vec_to_state_getElem]
      simp [hnone]
    rw [hnone, h1_goal_value, h_1]
    simp only [h_1_iter_fix_replace_goal]
    rw [show (replace_goal p (singletonVarSet f)).goal' = singletonVarSet f from rfl,
      if_neg hnsat]
    rfl

/-! ### The fast precondition-choice function -/

/-- The `h_1`-maximiser precondition-choice function, computed from the precomputed value
vector `h1Values` instead of one `h_1` fixpoint per precondition. -/
def h1_pcf_of (p : PlanningTask (n + 2)) (hp : has_preconditions p)
    (vals : Vector ℕ (n + 2)) : precondition_choice_function p :=
  fun a =>
    let l := a.val.pre.toList
    have hne : l ≠ [] := hp a.val a.property
    let f := (l.argmax (fun i => vals[i])).get (by
      rw [Option.isSome_iff_ne_none]
      intro h
      exact hne (List.argmax_eq_none.mp h))
    ⟨f, mem_pre_of_mem_pre_val a.val (List.argmax_mem (Option.get_mem _))⟩

/-- The `h_1`-maximiser precondition-choice function.  The value vector is an argument of
`h1_pcf_of`, so that it is computed once per precondition-choice function and not once per
action. -/
def h1_pcf_fast :
    Π p : PlanningTask (n + 2), has_preconditions p → precondition_choice_function p :=
  fun p hp => h1_pcf_of p hp (h1Values p)

/-- The fast precondition-choice function is the original one. -/
theorem h1_pcf_fast_eq (p : PlanningTask (n + 2)) (hp : has_preconditions p) :
    h1_pcf_fast p hp = h1_pcf p hp := by
  funext a
  apply Subtype.ext
  show ((a.val.pre.toList.argmax (fun i => (h1Values p)[i])).get _ : Fin (n + 2))
    = h1_argmax_pre p a.val (hp a.val a.property)
  have hfun : (fun i => (h1Values p)[i]) = (fun i => h1_goal_value p i) := by
    funext i
    exact h1Values_eq p i
  simp only [hfun, h1_argmax_pre]

/-! ### The heuristic -/

/-- **The LM-cut heuristic, computed with the fast precondition-choice function.** -/
def lmcut_fast (prob : PlanningTask n) (s : BitVec n) : ℕ∞ :=
  lmcut prob s h1_pcf_fast

/-- `lmcut_fast` is `lmcut` with the `h_1`-maximiser precondition-choice function. -/
theorem lmcut_fast_eq (prob : PlanningTask n) (s : BitVec n) :
    lmcut_fast prob s = lmcut prob s h1_pcf := by
  unfold lmcut_fast
  congr 1
  funext p hp
  exact h1_pcf_fast_eq p hp

end STRIPS
