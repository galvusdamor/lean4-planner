import pddl.Grounding.Correct
import Strips.PlanningTask

/-!
# From a ground task to `STRIPS.PlanningTask`

The intermediate representation `PDDL.GroundTask` of `pddl.Grounding.Task` is translated to
the `STRIPS.PlanningTask` interface of the `strips` library: the propositional variables are
the ground atoms `T.atoms` of the task (in the order in which they are collected), so that
variable `i` stands for the atom `T.atoms[i]`.

A STRIPS operator has a single unconditional add and delete list and a purely positive
precondition, and a STRIPS task has a conjunctive goal.  The translation is therefore only
defined for tasks that are `GroundTask.StripsReady`, i.e. unconditional, positive and with
a single goal clause.  Tasks with negative conditions can be brought into this form first
by the verified positive normal form compilation of `pddl.Grounding.Positive`.

The main results are

* `GroundTask.applicable_toAction_iff`, `GroundTask.encode_result`,
  `GroundTask.goalState_iff`: the step relation, applicability and the goal test agree
  under the encoding `GroundTask.encode` of states;
* `GroundTask.path_of_execution` and `GroundTask.execution_of_path`: executions of the
  ground task and paths of the STRIPS task correspond;
* `GroundTask.strips_solvable_iff`: the STRIPS task is solvable exactly when the ground
  task is; combined with `PDDL.groundInstance_solvable_iff` this connects a PDDL instance
  to the STRIPS interface.

Note that `STRIPS.Action` uses natural number costs, so the (nonnegative) integer costs of
the ground task are transported with `Int.toNat`.
-/

namespace PDDL

namespace GroundTask

variable (T : GroundTask)

/-- The number of propositional variables of the translated task. -/
abbrev numVars (T : GroundTask) : Nat := T.atoms.length

/-- The variable set corresponding to a list of atoms. -/
def varSetOf (T : GroundTask) (l : List Atom) : STRIPS.VarSet T.numVars :=
  STRIPS.VarSet.ofFn (fun i => decide (T.atoms[i.1]'i.2 ∈ l))

@[simp] theorem mem_varSetOf {T : GroundTask} {l : List Atom} {i : Fin T.numVars} :
    i ∈ T.varSetOf l ↔ T.atoms[i.1]'i.2 ∈ l := by
  simp [varSetOf]

/-! ### An efficient implementation of `varSetOf`

Read literally, `varSetOf` recomputes the atom list `T.atoms` (a deduplication of all atoms
occurring in the task) for *every single bit* of the variable set, which makes building the
STRIPS task quadratic in the size of the task with a very large constant.  The following
implementation computes the atom list once and indexes into it through an array; the `csimp`
lemma below makes the compiler use it for `varSetOf`, and hence for `toAction` and
`toSTRIPS`, without changing anything about the statements proved for them. -/

/-- The variable set of a list of atoms, given the atoms of the task as an array. -/
def varSetOfArr (n : Nat) (arr : Array Atom) (h : arr.size = n) (l : List Atom) :
    STRIPS.VarSet n :=
  STRIPS.VarSet.ofFn (fun i => decide (arr[i.1]'(by rw [h]; exact i.isLt) ∈ l))

/-- The efficient implementation of `GroundTask.varSetOf`. -/
def varSetOfFast (T : GroundTask) (l : List Atom) : STRIPS.VarSet T.numVars :=
  varSetOfArr T.numVars T.atoms.toArray (by simp [numVars]) l

@[csimp] theorem varSetOf_eq_fast : @varSetOf = @varSetOfFast := by
  funext T l
  unfold varSetOfFast varSetOfArr varSetOf
  congr 1

/-- The STRIPS state corresponding to a state of the ground task. -/
def encode (T : GroundTask) (s : State) : STRIPS.State T.numVars :=
  {i | T.atoms[i.1]'i.2 ∈ s}

@[simp] theorem mem_encode {T : GroundTask} {s : State} {i : Fin T.numVars} :
    i ∈ T.encode s ↔ T.atoms[i.1]'i.2 ∈ s := Iff.rfl

/-- A list of atoms contained in `T.atoms` is included in a state exactly when the
corresponding variable set is included in the encoded state. -/
theorem subset_encode_iff {T : GroundTask} {l : List Atom} {s : State}
    (hl : ∀ a ∈ l, a ∈ T.atoms) :
    (SetLike.coe (T.varSetOf l) ⊆ T.encode s) ↔ ∀ a ∈ l, a ∈ s := by
  constructor
  · intro h a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 (hl a ha)
    have hmem : (⟨i, hi⟩ : Fin T.numVars) ∈ T.varSetOf l := mem_varSetOf.2 ha
    exact h (SetLike.mem_coe.2 hmem)
  · intro h i hi
    exact h _ (mem_varSetOf.1 (SetLike.mem_coe.1 hi))

/-- The STRIPS operator corresponding to a ground operator. -/
def toAction (T : GroundTask) (op : GroundOp) : STRIPS.Action T.numVars where
  name := op.action.toString
  pre := T.varSetOf op.preAtoms
  add := T.varSetOf op.addList
  del := T.varSetOf op.delList
  cost := op.cost.toNat

/-- The STRIPS planning task corresponding to a ground task. -/
def toSTRIPS (T : GroundTask) : STRIPS.PlanningTask T.numVars where
  varNames := ⟨(T.atoms.map (·.toString)).toArray, by simp [numVars]⟩
  actions' := T.ops.map T.toAction
  init' := T.varSetOf T.init
  goal' := T.varSetOf T.goalAtoms

/-! ### An efficient implementation of `toSTRIPS`

Building one variable set bit by bit costs `O(numVars)` bit operations on a bit vector of
`numVars` bits, i.e. `O(numVars ^ 2)` word operations, which dominates the translation of a
large task.  The implementation below instead builds, once for the whole task, a hash map
from the atoms of the task to their index, and then sets exactly the bits of the atoms that
occur in the list.  Again, this is installed with `@[csimp]`, so nothing that is proved
about `toSTRIPS` changes. -/

/-- The variable set of a list of atoms, computed from a map from atoms to their index. -/
def varSetOfIdx (n : Nat) (idx : Std.HashMap Atom Nat) (l : List Atom) : STRIPS.VarSet n :=
  STRIPS.VarSet.ofList (l.filterMap (fun a =>
    (idx[a]?).bind (fun i => if h : i < n then some (⟨i, h⟩ : Fin n) else none)))

/-- The map from the atoms of a task to their index. -/
def atomIndex (T : GroundTask) : Std.HashMap Atom Nat := Std.HashMap.ofList T.atoms.zipIdx

theorem atomIndex_keys_pairwise (T : GroundTask) :
    T.atoms.zipIdx.Pairwise (fun x y : Atom × Nat => (x.1 == y.1) = false) := by
  have h : (T.atoms.zipIdx.map Prod.fst).Pairwise (fun a b : Atom => (a == b) = false) := by
    rw [List.zipIdx_map_fst]
    refine List.Pairwise.imp ?_ T.atoms_nodup
    intro a b hab
    simpa using hab
  rwa [List.pairwise_map] at h

/-- The index map is correct: it maps an atom of the task to its position in the atom
list, and every other atom to nothing. -/
theorem atomIndex_eq_some_iff {T : GroundTask} {a : Atom} {i : Nat} :
    (T.atomIndex)[a]? = some i ↔ T.atoms[i]? = some a := by
  constructor
  · intro h
    by_cases hmem : a ∈ T.atoms
    · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hmem
      have hk' : (T.atomIndex)[a]? = some k :=
        Std.HashMap.getElem?_ofList_of_mem (k := a) (k' := a) (beq_self_eq_true a)
          (T.atomIndex_keys_pairwise) (List.mk_mem_zipIdx_iff_getElem?.2 hk)
      rw [hk'] at h
      cases h
      exact hk
    · have : ((T.atoms.zipIdx.map Prod.fst).contains a) = false := by
        rw [List.zipIdx_map_fst]
        simpa using hmem
      rw [atomIndex, Std.HashMap.getElem?_ofList_of_contains_eq_false this] at h
      exact absurd h (by simp)
  · intro h
    exact Std.HashMap.getElem?_ofList_of_mem (k := a) (k' := a) (beq_self_eq_true a)
      (T.atomIndex_keys_pairwise) (List.mk_mem_zipIdx_iff_getElem?.2 h)

@[simp] theorem mem_varSetOfIdx {T : GroundTask} {l : List Atom} {i : Fin T.numVars} :
    i ∈ varSetOfIdx T.numVars T.atomIndex l ↔ T.atoms[i.1]'i.2 ∈ l := by
  rw [varSetOfIdx, STRIPS.VarSet.mem_ofList, List.mem_filterMap]
  constructor
  · rintro ⟨a, hal, ha⟩
    cases hidx : (T.atomIndex)[a]? with
    | none => rw [hidx] at ha; simp at ha
    | some j =>
      rw [hidx, Option.bind_some] at ha
      by_cases hj : j < T.numVars
      · rw [dif_pos hj] at ha
        have hji : j = i.1 := by
          exact congrArg Fin.val (Option.some.inj ha)
        have hget : T.atoms[j]? = some a := atomIndex_eq_some_iff.1 hidx
        rw [hji] at hget
        have : T.atoms[i.1]'i.2 = a := by
          rw [List.getElem?_eq_getElem i.2] at hget
          exact Option.some.inj hget
        rw [this]
        exact hal
      · rw [dif_neg hj] at ha
        exact absurd ha (by simp)
  · intro h
    refine ⟨T.atoms[i.1]'i.2, h, ?_⟩
    have hidx : (T.atomIndex)[T.atoms[i.1]'i.2]? = some i.1 :=
      atomIndex_eq_some_iff.2 (List.getElem?_eq_getElem i.2)
    rw [hidx, Option.bind_some, dif_pos i.2]

theorem varSetOf_eq_varSetOfIdx (T : GroundTask) (l : List Atom) :
    T.varSetOf l = varSetOfIdx T.numVars T.atomIndex l := by
  apply SetLike.coe_injective
  ext i
  simp only [SetLike.mem_coe, mem_varSetOf, mem_varSetOfIdx]

/-- The efficient implementation of `GroundTask.toSTRIPS`: the atom list and the index map
are computed once for the whole task. -/
def toSTRIPSFast (T : GroundTask) : STRIPS.PlanningTask T.numVars :=
  let atoms := T.atoms
  let n := atoms.length
  let idx : Std.HashMap Atom Nat := Std.HashMap.ofList atoms.zipIdx
  let vs : List Atom → STRIPS.VarSet n := varSetOfIdx n idx
  { varNames := ⟨(atoms.map (·.toString)).toArray, by simp [atoms, numVars]⟩
    actions' := T.ops.map (fun op =>
      { name := op.action.toString
        pre := vs op.preAtoms
        add := vs op.addList
        del := vs op.delList
        cost := op.cost.toNat })
    init' := vs T.init
    goal' := vs T.goalAtoms }

@[csimp] theorem toSTRIPS_eq_fast : @toSTRIPS = @toSTRIPSFast := by
  funext T
  have hvs : ∀ l, T.varSetOf l = varSetOfIdx T.numVars T.atomIndex l :=
    varSetOf_eq_varSetOfIdx T
  have hact : T.toAction = fun op : GroundOp =>
      ({ name := op.action.toString
         pre := varSetOfIdx T.numVars T.atomIndex op.preAtoms
         add := varSetOfIdx T.numVars T.atomIndex op.addList
         del := varSetOfIdx T.numVars T.atomIndex op.delList
         cost := op.cost.toNat } : STRIPS.Action T.numVars) := by
    funext op
    simp only [toAction, hvs]
  simp only [toSTRIPS, toSTRIPSFast, atomIndex, numVars, hvs, hact]

@[simp] theorem toSTRIPS_init (T : GroundTask) : T.toSTRIPS.init = T.encode T.initState := by
  ext i
  simp only [STRIPS.PlanningTask.init, toSTRIPS, SetLike.mem_coe, mem_varSetOf, mem_encode,
    initState, Set.mem_setOf_eq]

theorem mem_toSTRIPS_actions {T : GroundTask} {op : GroundOp} (hop : op ∈ T.ops) :
    T.toAction op ∈ T.toSTRIPS.actions :=
  STRIPS.PlanningTask.mem_actions'.1 (List.mem_map_of_mem hop)

theorem exists_op_of_mem_actions {T : GroundTask} {a : STRIPS.Action T.numVars}
    (ha : a ∈ T.toSTRIPS.actions) : ∃ op ∈ T.ops, a = T.toAction op := by
  obtain ⟨op, hop, rfl⟩ := List.mem_map.1 (STRIPS.PlanningTask.mem_actions'.2 ha)
  exact ⟨op, hop, rfl⟩

/-- Applicability agrees under the encoding, for operators with positive preconditions. -/
theorem applicable_toAction_iff {T : GroundTask} {op : GroundOp} (hop : op ∈ T.ops)
    (hpos : op.Positive) (s : State) :
    STRIPS.Applicable (T.encode s) (T.toAction op) ↔ op.Applicable s := by
  rw [GroundOp.applicable_of_positive hpos]
  exact subset_encode_iff (fun _ ha =>
    mem_atoms_of_mem_op hop (GroundOp.mem_atomList_of_mem_preAtoms ha))

/-- The goal test agrees under the encoding, for a positive conjunctive goal. -/
theorem goalState_iff {T : GroundTask} (hc : T.ConjunctiveGoal)
    (hp : ∀ c ∈ T.goal, ∀ l ∈ c, l.IsPos) (s : State) :
    T.toSTRIPS.GoalState (T.encode s) ↔ T.GoalHolds s := by
  rw [goalHolds_of_conjunctive_positive hc hp]
  exact subset_encode_iff (fun _ ha => mem_atoms_of_mem_goalAtoms ha)

/-- The successor state agrees under the encoding, for operators without conditional
effects. -/
theorem encode_result {T : GroundTask} {op : GroundOp}
    (huc : op.Unconditional) (s : State) :
    T.encode (op.result s) =
      (T.encode s \ SetLike.coe (T.toAction op).del) ∪ SetLike.coe (T.toAction op).add := by
  ext i
  simp only [mem_encode, GroundOp.mem_result, GroundOp.addSet_of_unconditional huc,
    GroundOp.delSet_of_unconditional huc, Set.mem_setOf_eq, Set.mem_union, Set.mem_sdiff,
    SetLike.mem_coe, toAction, mem_varSetOf]
  grind

/-! ### Executions and paths -/

/-- Every execution of the ground task gives a path in the STRIPS task. -/
theorem path_of_execution {T : GroundTask} (hready : T.StripsReady) {s s' : State}
    {π : List GroundOp} (h : T.Execution s π s') :
    Nonempty (STRIPS.PlanningTask.Path T.toSTRIPS (T.encode s) (T.encode s')) := by
  induction h with
  | nil s => exact ⟨.empty _⟩
  | @cons s s' op π hop happ _ ih =>
    obtain ⟨p⟩ := ih
    refine ⟨.cons (T.toAction op) (T.encode (op.result s)) (mem_toSTRIPS_actions hop)
      ⟨(applicable_toAction_iff hop (hready.positive.1 op hop) s).2 happ, ?_⟩ p⟩
    exact encode_result (hready.unconditional op hop) s

/-- Every path of the STRIPS task starting in an encoded state gives an execution of the
ground task. -/
theorem execution_of_path {T : GroundTask} (hready : T.StripsReady) :
    ∀ {S S' : STRIPS.State T.numVars} (_ : STRIPS.PlanningTask.Path T.toSTRIPS S S')
      (s : State), S = T.encode s →
      ∃ (π : List GroundOp) (s' : State), T.Execution s π s' ∧ S' = T.encode s' := by
  intro S S' p
  induction p with
  | empty S => intro s hs; exact ⟨[], s, Execution.nil s, hs⟩
  | @cons a S1 S2 S3 ha succ p ih =>
    intro s hs
    obtain ⟨op, hop, rfl⟩ := exists_op_of_mem_actions ha
    obtain ⟨happ, hsucc⟩ := succ
    subst hs
    have happ' : op.Applicable s :=
      (applicable_toAction_iff hop (hready.positive.1 op hop) s).1 happ
    have hS2 : S2 = T.encode (op.result s) := by
      rw [hsucc, encode_result (hready.unconditional op hop) s]
    obtain ⟨π, s', hexec, hs'⟩ := ih _ hS2
    exact ⟨op :: π, s', Execution.cons hop happ' hexec, hs'⟩

/-- The translation preserves plans: a plan of the ground task yields a plan of the STRIPS
task. -/
theorem strips_plan_of_isPlan {T : GroundTask} (hready : T.StripsReady) {π : List GroundOp}
    (h : T.IsPlan π) :
    Nonempty (STRIPS.PlanningTask.Plan T.toSTRIPS T.toSTRIPS.init) := by
  obtain ⟨s, hexec, hgoal⟩ := h
  obtain ⟨p⟩ := path_of_execution hready hexec
  refine ⟨⟨T.encode s, ?_, (goalState_iff hready.conjGoal hready.positive.2 s).2 hgoal⟩⟩
  rw [toSTRIPS_init]
  exact p

/-- The translation reflects plans: a plan of the STRIPS task yields a plan of the ground
task. -/
theorem isPlan_of_strips_plan {T : GroundTask} (hready : T.StripsReady)
    (p : STRIPS.PlanningTask.Plan T.toSTRIPS T.toSTRIPS.init) : ∃ π, T.IsPlan π := by
  obtain ⟨last, path, hgoal⟩ := p
  rw [toSTRIPS_init] at path
  obtain ⟨π, s', hexec, hs'⟩ := execution_of_path hready path T.initState rfl
  refine ⟨π, s', hexec, (goalState_iff hready.conjGoal hready.positive.2 s').1 ?_⟩
  rw [← hs']
  exact hgoal

/-- The STRIPS translation is solvable exactly when the ground task is. -/
theorem strips_solvable_iff {T : GroundTask} (hready : T.StripsReady) :
    Nonempty (STRIPS.PlanningTask.Plan T.toSTRIPS T.toSTRIPS.init) ↔ T.Solvable := by
  constructor
  · rintro ⟨p⟩
    exact isPlan_of_strips_plan hready p
  · rintro ⟨π, hπ⟩
    exact strips_plan_of_isPlan hready hπ

end GroundTask

/-- **Grounding a PDDL instance into the STRIPS interface preserves solvability.**  The
translated task is solvable exactly when the original lifted PDDL instance is. -/
theorem groundInstance_strips_solvable_iff {I : Instance}
    (hwf : I.domain.typesWellFormedB = true) {T : GroundTask}
    (h : groundInstance I = some T) (hready : T.StripsReady) :
    Nonempty (STRIPS.PlanningTask.Plan T.toSTRIPS T.toSTRIPS.init) ↔ I.Solvable := by
  rw [GroundTask.strips_solvable_iff hready, groundInstance_solvable_iff hwf h]

end PDDL
