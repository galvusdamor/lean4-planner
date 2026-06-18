import planning.LandmarkCutting

/-!
# A general LM-cut heuristic for arbitrary STRIPS problems and states

`lmcut_inner` (see `planning/LandmarkCutting.lean`) only computes a heuristic estimate for the
*initial* state of a problem that is already in i/g normal form (so that it has a unitary initial
state and a unitary goal).

This file packages it into a genuine heuristic `lmcut prob s pcf` that works for **any** STRIPS
problem `prob` and **any** state `s`:

1. it sets the initial state of `prob` to `s` (via `set_init`),
2. it applies the i/g normal form (`i_g_normal_form`), which produces a problem with a unitary
   initial state and a unitary goal,
3. it runs `lmcut_inner` on the result.

The precondition-choice function `pcf` is kept as a parameter (now over the `(n+2)`-variable normal
form).  We prove that `lmcut` is admissible: it never overestimates the cost of any plan of `prob`
starting from `s`.

The key technical ingredient is `ignf_plan_lift`: any plan of a problem `P` from its initial state
lifts to a plan of `i_g_normal_form P` from *its* initial state with the **same** cost (replay the
plan after the free `init` action and close it with the free `goal` action).  Combined with
`lmcut_inner_admissible_for_init`, admissibility follows.
-/

namespace Validator

open List

set_option maxHeartbeats 1000000

/-! ### The embedding of original variables into the i/g normal form -/

/-- The embedding of original variables `Fin n` into the i/g normal form `Fin (n+2)`. -/
def ignf_embF (n : ℕ) : Fin n → Fin (n + 2) := Fin.castLE (by omega)

lemma ignf_embF_injective (n : ℕ) : Function.Injective (ignf_embF n) :=
  Fin.castLE_injective _

@[simp] lemma ignf_embF_val (n : ℕ) (x : Fin n) : (ignf_embF n x).val = x.val := rfl

/-- The auxiliary `i` ("init") variable of the normal form. -/
def ignf_iFin (n : ℕ) : Fin (n + 2) := ⟨n, by omega⟩

/-- The auxiliary `g` ("goal") variable of the normal form. -/
def ignf_gFin (n : ℕ) : Fin (n + 2) := ⟨n + 1, by omega⟩

lemma ignf_iFin_not_mem_image (n : ℕ) (S : State n) : ignf_iFin n ∉ ignf_embF n '' S := by
  rintro ⟨x, -, hx⟩
  have hval : (ignf_embF n x).val = (ignf_iFin n).val := congrArg Fin.val hx
  simp only [ignf_embF_val, ignf_iFin] at hval
  exact absurd hval (Nat.ne_of_lt x.isLt)

/-- A state of `P` lifted into the normal form: the embedded facts together with the auxiliary
`i` variable. -/
def ignf_lift_state {n : ℕ} (S : State n) : State (n + 2) :=
  ignf_embF n '' S ∪ {ignf_iFin n}

/-! ### Action embeddings in the normal form -/

/-
Each original action of `P` appears, embedded, in the normal form, with the auxiliary `i`
variable added as a precondition and all its effects embedded.
-/
lemma ignf_embedded_action {n : ℕ} (P : STRIPS n) {a : Action n} (ha : a ∈ P.actions') :
    ∃ e : Action (n + 2), e ∈ (i_g_normal_form P).actions ∧
      e.cost = a.cost ∧
      e.pre = ignf_embF n '' a.pre ∪ {ignf_iFin n} ∧
      e.add = ignf_embF n '' a.add ∧
      e.del = ignf_embF n '' a.del := by
  simp +decide [ STRIPS.actions, i_g_normal_form ]
  refine' Or.inr ( Or.inr ⟨ a, ha, rfl, _, _, _ ⟩ ) <;> simp +decide [ ignf_embF, ignf_iFin ]
  · simp +decide [ Action.pre, convertVarSet ]
    rfl
  · ext; simp [Action.add, convertVarSet]
  · ext; simp [Action.del, convertVarSet]

/-
The `init` action of the normal form: its precondition is exactly the auxiliary `i` variable,
its add effect is the embedded initial state of `P`, it deletes nothing, and is free.
-/
lemma ignf_init_action {n : ℕ} (P : STRIPS n) :
    ∃ aI : Action (n + 2), aI ∈ (i_g_normal_form P).actions ∧
      aI.pre = {ignf_iFin n} ∧
      aI.add = ignf_embF n '' (convertState P.init') ∧
      aI.del = ∅ ∧
      aI.cost = 0 := by
  simp +decide [ STRIPS.actions, i_g_normal_form ]
  refine Or.inl ⟨ ?_, ?_, ?_ ⟩ <;> simp +decide [ Action.pre, Action.add, Action.del ]
  · unfold convertVarSet
    simp_all only [toFinset_cons, toFinset_nil, insert_empty_eq, Finset.coe_singleton, Set.singleton_eq_singleton_iff]
    rfl
  · ext; simp [convertVarSet, convertState, ignf_embF]
    simp +decide [ varset'_of_state', Fin.castLE ]
  · simp +decide [ convertVarSet ]

/-
The `goal` action of the normal form: its precondition is the embedded goal of `P`, its only add
effect is the auxiliary `g` variable, it deletes nothing, and is free.
-/
lemma ignf_goal_action {n : ℕ} (P : STRIPS n) :
    ∃ aG : Action (n + 2), aG ∈ (i_g_normal_form P).actions ∧
      aG.pre = ignf_embF n '' (convertVarSet P.goal') ∧
      aG.add = {ignf_gFin n} ∧
      aG.del = ∅ ∧
      aG.cost = 0 := by
  unfold i_g_normal_form; simp +decide [ STRIPS.actions, convertVarSet ] 
  refine Or.inr <| Or.inl ⟨ ?_, ?_, ?_ ⟩ <;> simp +decide [ Action.pre, Action.add, Action.del ]
  · ext; simp [convertVarSet, ignf_embF]
  · unfold convertVarSet
    simp_all only [toFinset_cons, toFinset_nil, insert_empty_eq, Finset.coe_singleton, Set.singleton_eq_singleton_iff]
    rfl
  · unfold convertVarSet
    simp_all only [toFinset_nil, Finset.coe_empty]

/-! ### Lifting paths and plans -/

/-
Applying an embedded action transforms a lifted state exactly as the original action transforms
the original state.  (The auxiliary `i` variable is never deleted since the embedded delete effects
only touch the embedded original variables.)
-/
lemma ignf_lift_successor {n : ℕ} (a : Action n) (S : State n) :
    ignf_lift_state ((S \ a.del) ∪ a.add)
      = (ignf_lift_state S \ (ignf_embF n '' a.del)) ∪ (ignf_embF n '' a.add) := by
  simp +decide [ Set.ext_iff, ignf_lift_state ]
  intro x; by_cases hx : x = ignf_iFin n <;> simp_all +decide [ ignf_embF ] 
  · exact Or.inl fun x hx => ne_of_lt <| Fin.castSucc_lt_last _
  · grind

/-- A path of `P` lifts to a path of `i_g_normal_form P` between the corresponding lifted states,
with the same cost. -/
lemma ignf_lift_path {n : ℕ} (P : STRIPS n) {S1 S2 : State n} (p : Path P S1 S2) :
    ∃ q : Path (i_g_normal_form P) (ignf_lift_state S1) (ignf_lift_state S2), q.cost = p.cost := by
  induction p with
  | empty s => exact ⟨Path.empty _, rfl⟩
  | cons a s2 ha succ p ih =>
    rename_i s1 s3
    obtain ⟨q, hq⟩ := ih
    obtain ⟨e, he_mem, he_cost, he_pre, he_add, he_del⟩ :=
      ignf_embedded_action P (mem_actions'_of_mem_actions ha)
    have hsucc : Successor e (ignf_lift_state s1) (ignf_lift_state s2) := by
      refine ⟨?_, ?_⟩
      · -- applicability
        show e.pre ⊆ _
        rw [he_pre, ignf_lift_state]
        exact Set.union_subset ((Set.image_mono succ.1).trans Set.subset_union_left)
          Set.subset_union_right
      · -- state transformation
        rw [succ.2, ignf_lift_successor a s1, he_del, he_add]
    exact ⟨Path.cons e (ignf_lift_state s2) he_mem hsucc q, by
      simp [Path.cost, hq, he_cost]⟩

/-- The cost of a concatenation of paths is the sum of the costs (public version). -/
lemma ignf_path_cost_append {n : ℕ} {pt : STRIPS n} {a b c : State n}
    (p : Path pt a b) (q : Path pt b c) : (p.append q).cost = p.cost + q.cost := by
  induction p with
  | empty s => simp [Path.append, Path.cost]
  | cons a' s2 ha succ p ih => simp [Path.append, Path.cost, ih]; ring

/-- The free `init` action moves from the normal form's initial state `{i}` to the lifted initial
state of `P`, at cost `0`. -/
lemma ignf_init_step {n : ℕ} (P : STRIPS n) :
    ∃ q : Path (i_g_normal_form P) (i_g_normal_form P).init
        (ignf_lift_state (convertState P.init')), q.cost = 0 := by
  obtain ⟨aI, haI_mem, haI_pre, haI_add, haI_del, haI_cost⟩ := ignf_init_action P
  have hsucc : Successor aI (i_g_normal_form P).init (ignf_lift_state (convertState P.init')) := by
    constructor
    · show aI.pre ⊆ _
      rw [haI_pre, i_g_normalform_init_eq]
      exact subset_rfl
    · show ignf_lift_state (convertState P.init') = ((i_g_normal_form P).init \ aI.del) ∪ aI.add
      rw [i_g_normalform_init_eq, haI_del, haI_add, Set.diff_empty, ignf_lift_state,
        Set.union_comm]
      rfl
  exact ⟨Path.cons aI (ignf_lift_state (convertState P.init')) haI_mem hsucc
    (Path.empty _), by simp [Path.cost, haI_cost]⟩

/-
The free `goal` action closes a plan: from the lifted state of any goal state of `P`, it reaches
a goal state of the normal form, at cost `0`.
-/
lemma ignf_goal_step {n : ℕ} (P : STRIPS n) {S : State n} (hg : P.GoalState S) :
    ∃ T : State (n + 2), (i_g_normal_form P).GoalState T ∧
      ∃ q : Path (i_g_normal_form P) (ignf_lift_state S) T, q.cost = 0 := by
  obtain ⟨aG, haG_mem, haG_pre, haG_add, haG_del, haG_cost⟩ := ignf_goal_action P
  refine ⟨(ignf_lift_state S \ aG.del) ∪ aG.add, ?_, ?_⟩
  · -- the result is a goal state of the normal form
    simp +decide [ STRIPS.GoalState, i_g_normal_form, haG_add, haG_del ]
    unfold convertVarSet; simp +decide [ ignf_gFin ] 
  · refine ⟨Path.cons aG _ haG_mem ⟨?_, rfl⟩ (Path.empty _), by simp [Path.cost, haG_cost]⟩
    -- applicability of the goal action
    show aG.pre ⊆ ignf_lift_state S
    rw [haG_pre, ignf_lift_state]
    exact (Set.image_mono hg).trans Set.subset_union_left

/-- **Plan lifting.**  Any plan of `P` from its initial state lifts to a plan of the i/g normal form
from *its* initial state, with the same cost. -/
lemma ignf_plan_lift {n : ℕ} (P : STRIPS n) (plan : Plan P P.init) :
    ∃ eplan : Plan (i_g_normal_form P) (i_g_normal_form P).init,
      eplan.path.cost = plan.path.cost := by
  obtain ⟨last, p, hgoal⟩ := plan
  obtain ⟨q0, hq0⟩ := ignf_init_step P
  obtain ⟨q1, hq1⟩ := ignf_lift_path P (S1 := convertState P.init') (S2 := last) p
  obtain ⟨T, hT, q2, hq2⟩ := ignf_goal_step P (S := last) hgoal
  refine ⟨⟨T, (q0.append q1).append q2, hT⟩, ?_⟩
  simp [ignf_path_cost_append, hq0, hq1, hq2]

/-- Replaying a path of `prob` in `set_init prob s` (only the initial state field differs, so the
actions are identical), preserving cost. -/
lemma path_set_init_transfer {n : ℕ} (prob : STRIPS n) (s : State' n) {s1 s2 : State n}
    (p : Path prob s1 s2) :
    ∃ q : Path (set_init prob s) s1 s2, q.cost = p.cost := by
  induction p with
  | empty t => exact ⟨Path.empty t, rfl⟩
  | cons a s2 ha succ p ih =>
    obtain ⟨q, hq⟩ := ih
    have hmem : a ∈ (set_init prob s).actions := by simpa [set_init, STRIPS.actions] using ha
    exact ⟨Path.cons a s2 hmem succ q, by simp [Path.cost, hq]⟩

/-! ### The general LM-cut heuristic -/

/-- The LM-cut heuristic for an arbitrary STRIPS problem `prob` evaluated at a state `s`.

It sets the initial state to `s`, applies the i/g normal form (yielding a problem with unitary
initial state and unitary goal), and runs `lmcut_inner`.  The precondition-choice function `pcf`
(over the `(n+2)`-variable normal form) is a parameter; it is only ever evaluated on problems with
preconditions (the i/g normal form and its cost partitions), so it is supplied a
`has_preconditions` proof.

If the goal is empty the problem is trivially solved and the heuristic returns `0`; this also avoids
the degenerate i/g normal form whose `goal` action would have an empty precondition. -/
def lmcut {n : ℕ} (prob : STRIPS n) (s : State' n)
    (pcf : Π p : STRIPS (n + 2), has_preconditions p → precondition_choice_function p) : ℕ :=
  if hg : prob.goal'.val = [] then 0
  else
    (lmcut_inner (i_g_normal_form (set_init prob s))
      (i_g_normalform_is_unitary_init _) (i_g_normalform_is_unitary_goal _)
      (i_g_normal_form_has_preconditions (set_init prob s) hg) pcf).2.1

/-- **Admissibility of the general LM-cut heuristic.**  `lmcut prob s pcf` never overestimates the
cost of any plan of `prob` starting from `s`. -/
theorem lmcut_admissible {n : ℕ} (prob : STRIPS n) (s : State' n)
    (pcf : Π p : STRIPS (n + 2), has_preconditions p → precondition_choice_function p)
    (plan : Plan prob (convertState s)) :
    plan.path.cost ≥ lmcut prob s pcf := by
  rw [lmcut]
  split
  · exact Nat.zero_le _
  · rename_i hg
    -- view the plan as a plan of `set_init prob s` from its initial state
    obtain ⟨p', hp'⟩ := path_set_init_transfer prob s plan.path
    obtain ⟨eplan, hcost⟩ :=
      ignf_plan_lift (set_init prob s) ⟨plan.last, p', plan.goal⟩
    have hadm := lmcut_inner_admissible_for_init (i_g_normal_form (set_init prob s))
      (i_g_normalform_is_unitary_init _) (i_g_normalform_is_unitary_goal _)
      (i_g_normal_form_has_preconditions (set_init prob s) hg) pcf eplan
    have he : eplan.path.cost = plan.path.cost := hcost.trans hp'
    exact he ▸ hadm

end Validator
