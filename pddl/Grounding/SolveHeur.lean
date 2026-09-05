import pddl.Grounding.Solve
import planning.PlannerCached
import planning.PlannerFast
import planning.LMCutH1PCF
import planning.H1Fast
import planning.LMCutFast
import planning.LMCutRun

/-!
# Choosing the heuristic of the PDDL solver

`pddl.Grounding.Solve` runs the A\* of the `planning` library with the blind heuristic.  This
module adds the possibility of choosing one of the heuristics of `planning`:

* `PDDL.Heur.blind` — the constant `0` heuristic (uniform-cost search), the default of
  `PDDL.solveOutcome`;
* `PDDL.Heur.h1` — the critical path heuristic `STRIPS.h_1` (`h^max`);
* `PDDL.Heur.h1fast` — the same heuristic computed by `STRIPS.h_1_fast`, which is proved to
  return the same value as `STRIPS.h_1` (`STRIPS.h_1_fast_eq`);
* `PDDL.Heur.lmcut` — the landmark-cut heuristic `STRIPS.lmcut` with the `h_1`-maximiser
  precondition-choice function `STRIPS.h1_pcf`;
* `PDDL.Heur.lmcutFast` — the same heuristic computed by `STRIPS.lmcut_fast`, proved equal to
  it (`STRIPS.lmcut_fast_eq`).

All of them are admissible (`PDDL.Heur.toFun_admissible`), so both guarantees of the solver
survive: `PDDL.solveOutcomeWith_isPlan` (a returned action sequence is a plan of the lifted
PDDL semantics) and `PDDL.solveOutcomeWith_unsolvable` (an instance reported unsolvable has no
plan).  With a non-trivial heuristic the search uses `STRIPS.planner_cached`, which memoises
the heuristic and is proved to return the same plan as the reference planner.
-/

namespace PDDL

open STRIPS

/-! ### The available heuristics -/

/-- The heuristics that the solver can be run with. -/
inductive Heur where
  /-- The blind heuristic `fun _ => 0` (uniform cost search). -/
  | blind
  /-- The critical path heuristic `STRIPS.h_1` (`h^max`). -/
  | h1
  /-- `STRIPS.h_1`, computed by the faster `STRIPS.h_1_fast`. -/
  | h1fast
  /-- The landmark cut heuristic with the `h_1`-maximiser precondition-choice function. -/
  | lmcut
  /-- The same landmark cut heuristic, computed by the faster `STRIPS.lmcut_fast`. -/
  | lmcutFast
  deriving DecidableEq, Repr, Inhabited

/-- Parse a heuristic name; unknown names give the blind heuristic. -/
def Heur.ofString (s : String) : Heur :=
  match s with
  | "h1" => .h1
  | "h1fast" => .h1fast
  | "lmcut" => .lmcut
  | "lmcutfast" => .lmcutFast
  | _ => .blind

/-- The heuristic function on the states of a STRIPS task. -/
def Heur.toFun (H : Heur) {n : ℕ} (prob : STRIPS.PlanningTask n) : BitVec n → ℕ∞ :=
  match H with
  | .blind => fun _ => 0
  | .h1 => fun s => (STRIPS.h_1 prob s : ℕ∞)
  | .h1fast => fun s => (STRIPS.h_1_fast prob s : ℕ∞)
  | .lmcut => fun s => STRIPS.lmcut prob s STRIPS.h1_pcf
  | .lmcutFast => fun s => STRIPS.lmcut_fast prob s

/-- Every available heuristic is admissible. -/
theorem Heur.toFun_admissible (H : Heur) {n : ℕ} (prob : STRIPS.PlanningTask n) :
    STRIPS.heur_admissible prob (H.toFun prob) := by
  cases H with
  | blind => intro v plan; exact bot_le
  | h1 => exact STRIPS.h_1_admissible prob
  | h1fast =>
      have : (fun s => ((STRIPS.h_1_fast prob s : ℕ) : ℕ∞))
          = (fun s => ((STRIPS.h_1 prob s : ℕ) : ℕ∞)) := by
        funext s; rw [STRIPS.h_1_fast_eq]
      simpa [Heur.toFun, this] using STRIPS.h_1_admissible prob
  | lmcut => intro v plan; exact STRIPS.lmcut_admissible prob v STRIPS.h1_pcf plan
  | lmcutFast =>
      intro v plan
      show STRIPS.lmcut_fast prob v ≤ _
      rw [STRIPS.lmcut_fast_eq]
      exact STRIPS.lmcut_admissible prob v STRIPS.h1_pcf plan

/-- Every available heuristic is admissible, in the graph formulation used by the planner's
completeness theorem. -/
theorem Heur.toFun_admissible' (H : Heur) {n : ℕ} (prob : STRIPS.PlanningTask n) :
    STRIPS.heur_admissible' prob (H.toFun prob) :=
  STRIPS.admissible'_of_admissible prob _ (H.toFun_admissible prob)

/-! ### The solver with a chosen heuristic -/

namespace GroundTask

/-- Solving a STRIPS-ready ground task with the A\* of the `planning` library, run with the
heuristic `H`, the memoising heuristic cache and the fact-indexed transition system
(`STRIPS.planner_cached_fast`). -/
def solveStripsHeur (T : GroundTask) (H : Heur) (te : ℕ := 0) : Option (List GroundOp) :=
  (STRIPS.planner_cached_fast T.toSTRIPS (H.toFun T.toSTRIPS) te).map T.planOps

/-- The memoising search returns the same result as the search used by `solveStripsWith`. -/
theorem solveStripsHeur_eq (T : GroundTask) (H : Heur) (te : ℕ) :
    T.solveStripsHeur H te = T.solveStripsWith (H.toFun T.toSTRIPS) te := by
  unfold solveStripsHeur solveStripsWith
  rw [STRIPS.planner_cached_fast_eq, STRIPS.planner_cached_eq_lazy]

/-- **Soundness**: the operator sequence returned by `solveStripsHeur` is a plan of the
ground task. -/
theorem solveStripsHeur_isPlan {T : GroundTask} (hready : T.StripsReady) {H : Heur} {te : ℕ}
    {π : List GroundOp} (h : T.solveStripsHeur H te = some π) : T.IsPlan π :=
  solveStripsWith_isPlan hready (by rwa [solveStripsHeur_eq] at h)

/-- **Completeness**: if `solveStripsHeur` returns nothing, the ground task is unsolvable. -/
theorem solveStripsHeur_unsolvable {T : GroundTask} (hready : T.StripsReady) {H : Heur}
    {te : ℕ} (h : T.solveStripsHeur H te = none) : ¬ T.Solvable :=
  solveStripsWith_unsolvable hready (H.toFun_admissible' T.toSTRIPS)
    (by rwa [solveStripsHeur_eq] at h)

end GroundTask

/-! ### The end to end solver with a chosen heuristic -/

/-- **The PDDL solver with a chosen heuristic**: as `PDDL.solveOutcome`, but the A\* search is
run with the heuristic `H` (and with the memoising search). -/
def solveOutcomeWith (I : Instance) (H : Heur) (groundFuel : Nat := 1000) (te : ℕ := 0) :
    SolveOutcome :=
  if I.domain.typesWellFormedB then
    match groundReachable I groundFuel with
    | none => .unknown
    | some T =>
      if T.unconditionalB && T.conjunctiveGoalB && T.negFreshB then
        match T.toPositive.solveStripsHeur H te with
        | some π => .plan (π.map (·.action))
        | none => .unsolvable
      else .unknown
    else .unknown

/-- **Soundness of the solver**: whenever it returns an action sequence, that sequence is a
plan of the lifted PDDL instance. -/
theorem solveOutcomeWith_isPlan {I : Instance} {H : Heur} {groundFuel : Nat} {te : ℕ}
    {σ : List GroundAction} (h : solveOutcomeWith I H groundFuel te = .plan σ) : I.IsPlan σ := by
  unfold solveOutcomeWith at h
  split at h
  · rename_i hwf
    cases hT : groundReachable I groundFuel with
    | none => rw [hT] at h; simp at h
    | some T =>
      rw [hT] at h
      dsimp only at h
      by_cases hchk : (T.unconditionalB && T.conjunctiveGoalB && T.negFreshB) = true
      · rw [if_pos hchk] at h
        have huc : T.Unconditional := GroundTask.unconditionalB_iff.1 (by simp_all)
        have hfresh : T.NegFresh := GroundTask.negFreshB_iff.1 (by simp_all)
        cases hs : T.toPositive.solveStripsHeur H te with
        | none => rw [hs] at h; simp at h
        | some π =>
          rw [hs] at h
          simp only [SolveOutcome.plan.injEq] at h
          subst h
          have hplan : T.toPositive.IsPlan π :=
            GroundTask.solveStripsHeur_isPlan
              (GroundTask.stripsReady_toPositive_of_checks hchk) hs
          obtain ⟨π₀, rfl, hπ₀⟩ :=
            GroundTask.isPlan_of_toPositive_isPlan hfresh huc hplan
          refine (groundReachable_isPlan_iff hwf hT _).2 ⟨π₀, ?_, hπ₀⟩
          exact (GroundTask.map_action_map_encOp π₀).symm ▸ rfl
      · rw [if_neg hchk] at h; simp at h
  · simp at h

/-- **Completeness of the solver**: an instance reported unsolvable really has no plan. -/
theorem solveOutcomeWith_unsolvable {I : Instance} {H : Heur} {groundFuel : Nat} {te : ℕ}
    (h : solveOutcomeWith I H groundFuel te = .unsolvable) : ¬ I.Solvable := by
  unfold solveOutcomeWith at h
  split at h
  · rename_i hwf
    cases hT : groundReachable I groundFuel with
    | none => rw [hT] at h; simp at h
    | some T =>
      rw [hT] at h
      dsimp only at h
      by_cases hchk : (T.unconditionalB && T.conjunctiveGoalB && T.negFreshB) = true
      · rw [if_pos hchk] at h
        have huc : T.Unconditional := GroundTask.unconditionalB_iff.1 (by simp_all)
        have hfresh : T.NegFresh := GroundTask.negFreshB_iff.1 (by simp_all)
        cases hs : T.toPositive.solveStripsHeur H te with
        | some π => rw [hs] at h; simp at h
        | none =>
          rw [groundReachable_solvable_iff hwf hT,
            ← GroundTask.toPositive_solvable_iff hfresh huc]
          exact GroundTask.solveStripsHeur_unsolvable
            (GroundTask.stripsReady_toPositive_of_checks hchk) hs
      · rw [if_neg hchk] at h; simp at h
  · simp at h

end PDDL
