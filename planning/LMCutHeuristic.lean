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

namespace STRIPS

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
lemma ignf_embedded_action {n : ℕ} (P : PlanningTask n) {a : Action n} (ha : a ∈ P.actions') :
    ∃ e : Action (n + 2), e ∈ (i_g_normal_form P).actions ∧
      e.cost = a.cost ∧
      (↑e.pre : Set (Fin (n+2))) = ignf_embF n '' (↑a.pre) ∪ {ignf_iFin n} ∧
      (↑e.add : Set (Fin (n+2))) = ignf_embF n '' (↑a.add) ∧
      (↑e.del : Set (Fin (n+2))) = ignf_embF n '' (↑a.del) := by
  revert ha;
  intro ha
  unfold i_g_normal_form;
  refine' ⟨ _, _, _, _, _ ⟩;
  exact ⟨ a.name, VarSet.ofList ( List.map ( Fin.castLE ( by omega ) ) a.pre.toList ++ [ ⟨ n, by omega ⟩ ] ), VarSet.ofList ( List.map ( Fin.castLE ( by omega ) ) a.add.toList ), VarSet.ofList ( List.map ( Fin.castLE ( by omega ) ) a.del.toList ), a.cost ⟩;
  · unfold PlanningTask.actions; aesop;
  · rfl;
  · ext x; simp [ignf_embF, ignf_iFin];
    grind;
  · constructor <;> ext x <;> simp +decide [ ignf_embF ]

lemma ignf_init_action {n : ℕ} (P : PlanningTask n) :
    ∃ aI : Action (n + 2), aI ∈ (i_g_normal_form P).actions ∧
      (↑aI.pre : Set (Fin (n+2))) = {ignf_iFin n} ∧
      (↑aI.add : Set (Fin (n+2))) = ignf_embF n '' (convertState P.init') ∧
      (↑aI.del : Set (Fin (n+2))) = ∅ ∧
      aI.cost = 0 := by
  refine' ⟨ _, _, _, _, _, _ ⟩;
  exact Action.mk "init" ( singletonVarSet ⟨ n, by omega ⟩ ) ( VarSet.ofList ( ( P.init' ).toList.map ( Fin.castLE ( by omega ) ) ) ) ( ∅ : VarSet ( n + 2 ) ) 0;
  · unfold i_g_normal_form; simp +decide [PlanningTask.actions];
  · exact Set.ext fun x => by simp +decide [ ignf_iFin, singletonVarSet ] ;
  · convert Set.ext _;
    simp +decide [ convertState, ignf_embF ];
  · aesop;
  · rfl

lemma ignf_goal_action {n : ℕ} (P : PlanningTask n) :
    ∃ aG : Action (n + 2), aG ∈ (i_g_normal_form P).actions ∧
      (↑aG.pre : Set (Fin (n+2))) = ignf_embF n '' (convertVarSet P.goal') ∧
      (↑aG.add : Set (Fin (n+2))) = {ignf_gFin n} ∧
      (↑aG.del : Set (Fin (n+2))) = ∅ ∧
      aG.cost = 0 := by
  refine' ⟨ _, _, _, _, _, _ ⟩;
  exact ⟨ "goal", VarSet.ofList ( P.goal'.toList |> List.map ( Fin.castLE ( by omega ) ) ), singletonVarSet ⟨ n + 1, by omega ⟩, ∅, 0 ⟩;
  · unfold i_g_normal_form; simp +decide [ PlanningTask.actions ] ;
  · ext x; simp [convertVarSet, ignf_embF];
  · convert Set.ext _;
    simp +decide [ ignf_gFin, singletonVarSet ];
  · aesop;
  · rfl

/-! ### Lifting paths and plans -/

/-
Applying an embedded action transforms a lifted state exactly as the original action transforms
the original state.  (The auxiliary `i` variable is never deleted since the embedded delete effects
only touch the embedded original variables.)
-/
lemma ignf_lift_successor {n : ℕ} (a : Action n) (S : State n) :
    ignf_lift_state ((S \ a.del) ∪ a.add)
      = (ignf_lift_state S \ (ignf_embF n '' a.del)) ∪ (ignf_embF n '' a.add) := by
  simp [ Set.ext_iff, ignf_lift_state ]
  intro x; by_cases hx : x = ignf_iFin n <;> simp_all [ ignf_embF ]
  · exact Or.inl fun x hx => ne_of_lt <| Fin.castSucc_lt_last _
  · grind

/-
A path of `P` lifts to a path of `i_g_normal_form P` between the corresponding lifted states,
with the same cost.
-/
lemma ignf_lift_path {n : ℕ} (P : PlanningTask n) {S1 S2 : State n} (p : PlanningTask.Path P S1 S2) :
    ∃ q : PlanningTask.Path (i_g_normal_form P) (ignf_lift_state S1) (ignf_lift_state S2), q.cost = p.cost := by
  revert p;
  intro p
  induction' p with S1 S2 a p ih;
  · exact ⟨ PlanningTask.Path.empty _, rfl ⟩;
  · rename_i h₁ h₂ h₃;
    obtain ⟨ q, hq ⟩ := h₃;
    obtain ⟨e, he⟩ : ∃ e : Action (n + 2), e ∈ (i_g_normal_form P).actions ∧ e.cost = S2.cost ∧ (↑e.pre : Set (Fin (n+2))) = ignf_embF n '' (↑S2.pre) ∪ {ignf_iFin n} ∧ (↑e.add : Set (Fin (n+2))) = ignf_embF n '' (↑S2.add) ∧ (↑e.del : Set (Fin (n+2))) = ignf_embF n '' (↑S2.del) := by
      convert ignf_embedded_action P _;
      (expose_names; exact mem_actions'_of_mem_actions ha);
    refine' ⟨ PlanningTask.Path.cons e ( ignf_lift_state p ) he.1 _ q, _ ⟩;
    constructor;
    all_goals simp_all +decide [ Applicable, PlanningTask.Path.cost ];
    · simp_all +decide [ Set.subset_def, ignf_lift_state ];
      intro x hx; specialize h₁; cases h₁; aesop;
    · convert ignf_lift_successor S2 a using 1

lemma ignf_path_cost_append {n : ℕ} {pt : PlanningTask n} {a b c : State n}
    (p : PlanningTask.Path pt a b) (q : PlanningTask.Path pt b c) : (p.append q).cost = p.cost + q.cost := by
  induction p with
  | empty s => simp [PlanningTask.Path.append, PlanningTask.Path.cost]
  | cons a' s2 ha succ p ih => simp only [PlanningTask.Path.append, PlanningTask.Path.cost]; rw [ih]; ring

/-
The free `init` action moves from the normal form's initial state `{i}` to the lifted initial
state of `P`, at cost `0`.
-/
lemma ignf_init_step {n : ℕ} (P : PlanningTask n) :
    ∃ q : PlanningTask.Path (i_g_normal_form P) (i_g_normal_form P).init
        (ignf_lift_state (convertState P.init')), q.cost = 0 := by
          -- The goal is to show that the cost of the path is zero, but the path is constructed by appending two paths, each with cost zero. This leads to a contradiction. Therefore, the assumption must be false.
          apply Classical.byContradiction
          intro h_contra;
          obtain ⟨aI, haI⟩ := ignf_init_action P;
          refine' h_contra ⟨ _, _ ⟩;
          exact PlanningTask.Path.cons aI ( ignf_lift_state ( convertState P.init' ) ) haI.1 ( by
            simp +decide [ Successor, haI ];
            unfold Applicable; simp +decide [ haI, ignf_lift_state ] ;
            unfold i_g_normal_form; simp +decide [ PlanningTask.init ] ;
            simp +decide [ ignf_iFin, ignf_embF, convertState ];
            grind ) ( PlanningTask.Path.empty _ )
          generalize_proofs at *;
          simp +decide [ PlanningTask.Path.cost, haI ]

lemma ignf_goal_step {n : ℕ} (P : PlanningTask n) {S : State n} (hg : P.GoalState S) :
    ∃ T : State (n + 2), (i_g_normal_form P).GoalState T ∧
      ∃ q : PlanningTask.Path (i_g_normal_form P) (ignf_lift_state S) T, q.cost = 0 := by
  refine' ⟨ _, _, _ ⟩;
  exact ignf_lift_state S ∪ { ignf_gFin n };
  · simp +decide [ PlanningTask.GoalState, i_g_normal_form, ignf_lift_state, ignf_gFin ];
    simp +decide [ convertVarSet, singletonVarSet ];
  · obtain ⟨aG, haG⟩ := ignf_goal_action P;
    use PlanningTask.Path.cons aG ( ignf_lift_state S ∪ { ignf_gFin n } ) haG.1 ( by
      unfold Successor; simp +decide [ haG ] ;
      unfold Applicable; simp +decide [ haG, ignf_lift_state ] ;
      intro x hx; specialize hg; unfold PlanningTask.GoalState at hg; aesop; ) ( PlanningTask.Path.empty _ );
    generalize_proofs at *;
    simp +decide [ PlanningTask.Path.cost, haG ];

lemma ignf_plan_lift {n : ℕ} (P : PlanningTask n) (plan : PlanningTask.Plan P P.init) :
    ∃ eplan : PlanningTask.Plan (i_g_normal_form P) (i_g_normal_form P).init,
      eplan.path.cost = plan.path.cost := by
        by_contra h_contra;
        obtain ⟨q, hq⟩ := ignf_lift_path P plan.path;
        obtain ⟨T, hT⟩ := ignf_goal_step P plan.goal;
        obtain ⟨eplan, heplan⟩ : ∃ eplan : PlanningTask.Path (i_g_normal_form P) (ignf_lift_state plan.last) T, eplan.cost = 0 := by
          exact hT.2;
        obtain ⟨q', hq'⟩ := ignf_init_step P;
        refine' h_contra ⟨ ⟨ _, _, _ ⟩, _ ⟩;
        exact T;
        exact q'.append ( q.append eplan );
        grind;
        rw [ ignf_path_cost_append, ignf_path_cost_append, hq', heplan, hq ] ; ring

lemma path_set_init_transfer {n : ℕ} (prob : PlanningTask n) (s : BitVec n) {s1 s2 : State n}
    (p : PlanningTask.Path prob s1 s2) :
    ∃ q : PlanningTask.Path (set_init prob s) s1 s2, q.cost = p.cost := by
  induction p with
  | empty t => exact ⟨PlanningTask.Path.empty t, rfl⟩
  | cons a s2 ha succ p ih =>
    obtain ⟨q, hq⟩ := ih
    have hmem : a ∈ (set_init prob s).actions := by simpa [set_init, PlanningTask.actions] using ha
    exact ⟨PlanningTask.Path.cons a s2 hmem succ q, by simp [PlanningTask.Path.cost, hq]⟩

/-! ### The general LM-cut heuristic -/

/-- The LM-cut heuristic for an arbitrary STRIPS problem `prob` evaluated at a state `s`.

It sets the initial state to `s`, applies the i/g normal form (yielding a problem with unitary
initial state and unitary goal), and runs `lmcut_inner`.  The precondition-choice function `pcf`
(over the `(n+2)`-variable normal form) is a parameter; it is only ever evaluated on problems with
preconditions (the i/g normal form and its cost partitions), so it is supplied a
`has_preconditions` proof.

If the goal is empty the problem is trivially solved and the heuristic returns `0`; this also avoids
the degenerate i/g normal form whose `goal` action would have an empty precondition. -/
def lmcut {n : ℕ} (prob : PlanningTask n) (s : BitVec n)
    (pcf : Π p : PlanningTask (n + 2), has_preconditions p → precondition_choice_function p) : ℕ∞ :=
  if hg : prob.goal'.toList = [] then 0
  else
    (lmcut_inner (i_g_normal_form (set_init prob s))
      (i_g_normalform_is_unitary_init _) (i_g_normalform_is_unitary_goal _)
      (i_g_normal_form_has_preconditions (set_init prob s) hg) pcf).2.1

/-- **Admissibility of the general LM-cut heuristic.**  `lmcut prob s pcf` never overestimates the
cost of any plan of `prob` starting from `s`. -/
theorem lmcut_admissible {n : ℕ} (prob : PlanningTask n) (s : BitVec n)
    (pcf : Π p : PlanningTask (n + 2), has_preconditions p → precondition_choice_function p)
    (plan : PlanningTask.Plan prob (convertState s)) :
    (plan.path.cost : ℕ∞) ≥ lmcut prob s pcf := by
  rw [ge_iff_le, lmcut]
  split_ifs with hg
  · exact zero_le _
  · obtain ⟨q, hq⟩ := path_set_init_transfer prob s plan.path
    let plan_si : PlanningTask.Plan (set_init prob s) (set_init prob s).init :=
      ⟨plan.last, q, plan.goal⟩
    obtain ⟨eplan, heplan⟩ := ignf_plan_lift (set_init prob s) plan_si
    have hadm := lmcut_inner_admissible_for_init (i_g_normal_form (set_init prob s))
      (i_g_normalform_is_unitary_init _) (i_g_normalform_is_unitary_goal _)
      (i_g_normal_form_has_preconditions (set_init prob s) hg) pcf eplan
    have h2 : plan_si.path.cost = plan.path.cost := hq
    have hcost : (eplan.path.cost : ℕ∞) = (plan.path.cost : ℕ∞) := by
      rw [heplan, h2]
    exact le_trans hadm (le_of_eq hcost)
