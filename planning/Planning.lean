import SearchAlgorithms.NatGraph
import Strips.PlanningTask
import Mathlib.Data.Set.Card
import planning.BitScan
--import Mathlib.Basic.Logic.Lemmas

namespace STRIPS
/-! ### Runtime layer for the public `strips` dependency

The public `strips` library (https://github.com/AmosNico/lean4-strips) represents finite
sets of variables by the concrete bit-vector-backed type `VarSet n`, while mathematical
states remain `State n = Set (Fin n)`.

The planning development uses `VarSet` directly for variable sets (including action
preconditions and effects) and `BitVec` for run-time states. The abstract `Set`-based
notions from `Strips` (`State`, `Successor`, `PlanningTask.GoalState`, ...) are used for
mathematical results and connected to the run-time layer by the bridging lemmas below. -/

/-- `getElem` of a `BitVec` obtained from a boolean list. -/
theorem BitVec.getElem_ofBoolListLE {i : Nat} {bs : List Bool} (h : i < bs.length) :
    (BitVec.ofBoolListLE bs)[i] = bs[i] := by
  rw [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofBoolListLE]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem h]
  simp

private lemma getElem_eq_rec_BitVec' {m n : ℕ} (h : m = n) (bv : BitVec m) (i : ℕ)
    (hi : i < n) :
    (show BitVec n from h ▸ bv)[i] = bv[i]'(by omega) := by
  subst h; rfl

instance instFinEnumBitVec {n : ℕ} : FinEnum (BitVec n) :=
  FinEnum.ofList (List.range (2^n)) (by
    intro x
    simp
    use BitVec.toNat x
    grind)

/-- Enumerate the variables in a runtime variable set. -/
def VarSet.val {n : ℕ} (V : VarSet n) : List (Fin n) :=
  (List.finRange n).filter (fun i => i ∈ V)

/-- **Enumerating a variable set by scanning its bit vector one machine word at a time.**

The filter of `VarSet.val` tests every one of the `n` variables, and each test shifts the whole
bit vector, so it costs `Θ(n²/64)` machine words; `bitScan` (see `planning.BitScan`) extracts
one 64-bit word per shift and skips a word without set bits in a single test.  Since
`VarSet.val` is what `VarSet.toList` enumerates, this is the hottest primitive of the
development: it is used by the `h^max` fixpoint, by the LM-cut precondition-choice function and
by the successor generator. -/
def VarSet.valFast {n : ℕ} (V : VarSet n) : List (Fin n) := bitScan V.toBitVec

/-- **The scan enumerates the variable set.** -/
@[csimp] theorem VarSet.val_eq_fast : @VarSet.val = @VarSet.valFast := by
  funext n V
  rw [VarSet.valFast, bitScan_eq, VarSet.val]
  apply List.filter_congr
  intro i _
  rw [Bool.eq_iff_iff, decide_eq_true_iff, VarSet.mem_iff, Fin.getElem_fin,
    BitVec.getElem_eq_testBit_toNat V.toBitVec i.val i.isLt]

@[simp] lemma VarSet.mem_val {n : ℕ} {V : VarSet n} {i : Fin n} :
    i ∈ V.val ↔ i ∈ V := by simp [VarSet.val]

@[simp] lemma mem_val_ofList {n : ℕ} {l : List (Fin n)} {i : Fin n} :
    i ∈ (VarSet.ofList l).val ↔ i ∈ l := by simp

@[simp] lemma val_emptyVarSet {n : ℕ} : (∅ : VarSet n).val = [] := by
  simp [VarSet.val]
@[simp] lemma mem_emptyVarSet {n : ℕ} {i : Fin n} : i ∈ (∅ : VarSet n).val ↔ False := by simp

/-- View a runtime variable set as the mathematical set of its members. -/
abbrev convertVarSet {n : ℕ} (V : VarSet n) : Set (Fin n) := V

/-- View a runtime bit-vector state as the mathematical set of its true variables. -/
def convertState {n : ℕ} (s : BitVec n) : State n := {i | s[i]}

@[simp] lemma convertVarSet_empty {n : ℕ} :
    convertVarSet (∅ : VarSet n) = (∅ : Set (Fin n)) := by ext i; simp [convertVarSet]

/-- The elements of a runtime variable set as a list. -/
def VarSet.toList {n : ℕ} (V : VarSet n) : List (Fin n) := V.val

@[simp] lemma VarSet.mem_toList {n : ℕ} {V : VarSet n} {i : Fin n} :
    i ∈ V.toList ↔ i ∈ V.val := Iff.rfl

@[simp] lemma VarSet.mem_toList_iff {n : ℕ} {V : VarSet n} {i : Fin n} :
    i ∈ V.toList ↔ i ∈ V := by simp only [VarSet.mem_toList, VarSet.mem_val]

@[simp] lemma mem_convertVarSet {n : ℕ} {V : VarSet n} {i : Fin n} :
    i ∈ convertVarSet V ↔ i ∈ V.val := by simp [convertVarSet]

@[simp] lemma mem_convertState {n : ℕ} {s : BitVec n} {i : Fin n} :
    i ∈ convertState s ↔ s[i.val] := Iff.rfl

lemma Action.mem_pre {n : ℕ} {a : Action n} {i : Fin n} :
    i ∈ a.pre ↔ i ∈ a.pre.val := by simp
lemma Action.mem_add {n : ℕ} {a : Action n} {i : Fin n} :
    i ∈ a.add ↔ i ∈ a.add.val := by simp
lemma Action.mem_del {n : ℕ} {a : Action n} {i : Fin n} :
    i ∈ a.del ↔ i ∈ a.del.val := by simp

lemma VarSet.toList_nodup {n : ℕ} (V : VarSet n) : V.toList.Nodup := by
  exact (List.nodup_finRange n).filter _

lemma VarSet.coe_toList_toFinset {n : ℕ} (V : VarSet n) :
    (↑V.toList.toFinset : Set (Fin n)) = convertVarSet V := by
  ext i; simp [convertVarSet]

lemma VarSet.toList_ne_nil_of_mem {n : ℕ} {V : VarSet n} {i : Fin n} (h : i ∈ V.val) :
    V.toList ≠ [] := by
  intro he
  have : i ∈ V.toList := by simpa using h
  simp [he] at this

lemma VarSet.ncard_convertVarSet_eq_toList_length {n : ℕ} (V : VarSet n) :
    (convertVarSet V).ncard = V.toList.length := by
  rw [← V.coe_toList_toFinset, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup V.toList_nodup]

/-- The singleton variable set `{f}` as a `VarSet`. -/
def singletonVarSet {n : ℕ} (f : Fin n) : VarSet n := VarSet.ofList [f]

@[simp] lemma mem_singletonVarSet {n : ℕ} {f i : Fin n} :
    i ∈ (singletonVarSet f).val ↔ i = f := by simp [singletonVarSet, VarSet.ofList]

lemma VarSet.eq_of_toList_eq {n : ℕ} {V W : VarSet n} (h : V.toList = W.toList) : V = W := by
  apply SetLike.coe_injective
  ext i
  simpa using congrArg (fun l => i ∈ l) h

@[simp] lemma VarSet.toList_singletonVarSet {n : ℕ} (f : Fin n) :
    (singletonVarSet f).toList = [f] := by
  have hmem : f ∈ (singletonVarSet f).toList := by
    simp only [VarSet.mem_toList, VarSet.mem_val]
    change f ∈ VarSet.ofList [f]
    simp
  have hlen : (singletonVarSet f).toList.length = 1 := by
    rw [← VarSet.ncard_convertVarSet_eq_toList_length]
    have heq : convertVarSet (singletonVarSet f) = ({f} : Set (Fin n)) := by
      ext i
      simp [singletonVarSet, VarSet.ofList, convertVarSet]
    rw [heq]
    simp
  rcases hlist : (singletonVarSet f).toList with _ | ⟨x, xs⟩
  · simp [hlist] at hmem
  · have hxs : xs = [] := by simpa [hlist] using hlen
    subst xs
    simp [hlist] at hmem
    subst x
    rfl

/-- The bit-vector obtained from a boolean predicate on `Fin n`. -/
def bvOfPred {n} (P : Fin n → Bool) : BitVec n :=
  (BitVec.ofBoolListLE ((List.finRange n).map P)).cast (by simp)

@[simp] lemma getElem_bvOfPred {n} (P : Fin n → Bool) (i : Fin n) :
    (bvOfPred P)[i.val] = P i := by
  unfold bvOfPred
  rw [BitVec.getElem_cast, BitVec.getElem_ofBoolListLE (by simp [i.isLt])]
  simp

lemma VarSet.getElem_toBitVec {n} (V : VarSet n) (i : Fin n) :
    V.toBitVec[i.val] = decide (i ∈ V.val) := by
  simp [VarSet.mem_iff]

lemma VarSet.getElem_toBitVec' {n} (V : VarSet n) (i : ℕ) (hi : i < n) :
    V.toBitVec[i]'hi = decide (⟨i, hi⟩ ∈ V.val) := VarSet.getElem_toBitVec V ⟨i, hi⟩

/-- Convert a `VarSet` to a run-time state (bit-vector). -/
def state'_of_varset' {n : ℕ} (V : VarSet n) : BitVec n := V.toBitVec

/-- Build the `VarSet` of variables that are true in a run-time state. -/
def varset'_of_state' {n : ℕ} (s : BitVec n) : VarSet n := ⟨s⟩

@[simp] lemma mem_varset'_of_state' {n : ℕ} (s : BitVec n) (i : Fin n) :
    i ∈ varset'_of_state' s ↔ s[i.val] = true := by
  simp [varset'_of_state', VarSet.mem_iff]

/-- The list of variables that are true in a run-time state. -/
def _root_.BitVec.toList {n : ℕ} (s : BitVec n) : List (Fin n) := (varset'_of_state' s).val

@[simp] lemma _root_.BitVec.mem_toList {n : ℕ} {s : BitVec n} {i : Fin n} :
    i ∈ s.toList ↔ s[i.val] := by
  simp [BitVec.toList, varset'_of_state', VarSet.mem_iff]

lemma _root_.BitVec.toList_nodup {n : ℕ} (s : BitVec n) : s.toList.Nodup :=
  (varset'_of_state' s).toList_nodup

/-- The coercion of the list of true variables of a state to a `Finset` equals its abstract set. -/
lemma _root_.BitVec.coe_toList_toFinset {n : ℕ} (s : BitVec n) :
    (↑s.toList.toFinset : Set (Fin n)) = convertState s := by
  ext i; simp

/-- The number of true variables of a state equals the length of its list of true variables. -/
lemma _root_.BitVec.ncard_convertState_eq_toList_length {n : ℕ} (s : BitVec n) :
    (convertState s).ncard = s.toList.length := by
  rw [← BitVec.coe_toList_toFinset, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup s.toList_nodup]

/-- `state'_of_varset'` at index `i` checks membership in the var-set. -/
@[simp] lemma state'_of_varset'_getElem {n : ℕ} (v : VarSet n) (i : Fin n) :
    (state'_of_varset' v)[i.val] = decide (i ∈ v.val) := by
  exact VarSet.getElem_toBitVec v i

/-- A variable is in `varset'_of_state'` iff it is true in the state. -/
@[simp] lemma varset'_of_state'_mem {n : ℕ} (s : BitVec n) (i : Fin n) :
    i ∈ (varset'_of_state' s).val ↔ s[i.val] = true := by
  simp [varset'_of_state', VarSet.mem_iff]

/-- A run-time state satisfies a set of conditions if all of them are true. -/
def satisfies' {n : ℕ} (cond : VarSet n) (state : BitVec n) : Bool :=
  decide (∀ i ∈ cond.val, state[i.val])

@[simp] lemma satisfies'_iff {n : ℕ} (cond : VarSet n) (state : BitVec n) :
    satisfies' cond state = true ↔ ∀ i ∈ cond.val, state[i.val] := by simp [satisfies']

/-- Bit-parallel implementation of `satisfies'`: a state satisfies a condition set iff the
condition bits are a subset of the state bits, which is one bitwise `and` and one comparison.

The declarative `satisfies'` enumerates `cond.val`, and `VarSet.val` builds and filters
`List.finRange n`, so evaluating it costs `Θ(n)` list allocations *per call*; in a search this
is by far the dominant cost, because the goal test and every applicability test go through it.
The two functions are equal (`satisfies'_eq_fast`), and the equation is installed with
`@[csimp]`, so the compiler uses this implementation for `satisfies'` everywhere and no result
about `satisfies'` has to change. -/
def satisfies'_fast {n : ℕ} (cond : VarSet n) (state : BitVec n) : Bool :=
  (cond.toBitVec &&& state) == cond.toBitVec

/-- `satisfies'` is the bit-parallel `satisfies'_fast`. -/
@[csimp] theorem satisfies'_eq_fast : @satisfies' = @satisfies'_fast := by
  funext n cond state
  rw [Bool.eq_iff_iff, satisfies'_iff]
  simp only [satisfies'_fast, beq_iff_eq, BitVec.eq_of_getElem_eq_iff, BitVec.getElem_and]
  constructor
  · intro h i hi
    by_cases hc : cond.toBitVec[i] = true
    · have hmem : (⟨i, hi⟩ : Fin n) ∈ cond.val := by
        simp only [VarSet.mem_val, VarSet.mem_iff]
        exact hc
      simp [hc, h ⟨i, hi⟩ hmem]
    · simp only [Bool.not_eq_true] at hc
      simp [hc]
  · intro h i hi
    have hc : cond.toBitVec[i.val] = true := by
      simpa only [VarSet.mem_val, VarSet.mem_iff, Fin.getElem_fin] using hi
    have h' := h i.val i.isLt
    rw [hc] at h'
    simpa using h'


def applicable' {n : ℕ} (a : Action n) (state : BitVec n) : Bool :=
  satisfies' a.pre state

lemma applicable'_iff {n : ℕ} (a : Action n) (state : BitVec n) :
    applicable' a state = true ↔ ∀ i ∈ a.pre.val, state[i.val] := by simp [applicable']

def successor' {n : ℕ} (a : Action n) (f : BitVec n) : BitVec n :=
  (f &&& ~~~a.del.toBitVec) ||| a.add.toBitVec

def is_successor' {n : ℕ} (a : Action n) (f t : BitVec n) : Bool :=
  decide (t = successor' a f)

-- regress a through s. Note that this returns the minimally necessary state for the regression to be possible
def regress' {n : ℕ} (a : Action n) (s : BitVec n) : BitVec n :=
  (s &&& ~~~a.add.toBitVec) ||| a.pre.toBitVec

-- an action can regress through a state if it does not delete anything that is true in the successor state
def regressable' {n : ℕ} (a : Action n) (s : BitVec n) : Bool :=
  decide (∀ i ∈ a.del.val, (¬ s[i.val] ∨ (state'_of_varset' a.add)[i.val]))

lemma successor'_is_successor' {n : ℕ} (a : Action n) (f : BitVec n) :
    is_successor' a f (successor' a f) := by
  simp [is_successor']


lemma is_successor'_eq_successor' {n : ℕ} (a : Action n) (f t : BitVec n)
    (h : is_successor' a f t = true) : t = successor' a f := by
  simpa [is_successor'] using h

lemma successor_regressable {n : ℕ} (a : Action n) (f : BitVec n):
    applicable' a f → regressable' a (successor' a f) := by
  unfold regressable'
  simp +decide [ BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not, successor' ]
  grind +suggestions
/-
f and (regress' a (successor' a f)) can differ in facts added and delete by a
-/
lemma successor_regress {n : ℕ} (a : Action n) (f : BitVec n) :
    applicable' a f → successor' a (regress' a (successor' a f)) = successor' a f := by
  intro h
  ext i hi
  have h_pre : ∀ j ∈ a.pre.val, f[j.val] := (applicable'_iff a f).mp h
  simp only [successor', regress', BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not,
    VarSet.getElem_toBitVec']
  by_cases hf : f[i]'hi <;> simp_all +decide
  · grind
  · intro hp; have := h_pre ⟨i, hi⟩ (by simpa using hp); simp_all

abbrev is_successor_state {n : ℕ} (prob : PlanningTask n) (f t : BitVec n) :=
    prob.actions'.any (fun a => applicable' a f ∧ is_successor' a f t)

def cost_of {n : ℕ} (prob : PlanningTask n) (f t : BitVec n) (is_succ : is_successor_state prob f t): ℕ :=
    let applicableActs := prob.actions'.filter (fun a => applicable' a f ∧ is_successor' a f t)
    let costs : List ℕ := applicableActs.map (fun x => x.cost)
    costs.min (by unfold costs applicableActs ; simp_all)


lemma min_fold_find {α β : Type u}  [LinearOrder β] (l : List α) (x : β) (f : α → β) (h : x ≠ List.foldl min (x) (List.map f l)):
  ∃ a ∈ l, f a = List.foldl min x (List.map f l) := by
  cases l
  · contradiction
  case cons head tail =>
    by_cases head_eq_min : f head = List.foldl min x (List.map f (head :: tail))
    · use head
      constructor
      · simp only [List.mem_cons, true_or]
      · exact head_eq_min
    ·
      unfold List.map List.foldl at ⊢ head_eq_min
      simp only [List.mem_cons, exists_eq_or_imp]
      right
      apply min_fold_find
      by_contra
      rw [←this] at head_eq_min
      have x_lt_head : x = x ⊓ f head := by
        expose_names
        rw [inst.min_def]
        grind
      grind

lemma min_map {α β : Type u} [LinearOrder β] (l : List α) (f : α → β) (h : l.map f ≠ []):
    ∃ a ∈ l, f a = (l.map f).min h := by
    cases l
    · grind
    · expose_names
      unfold List.min
      simp
      rw [or_iff_not_imp_left]; intro head_ne_min
      apply min_fold_find
      apply head_ne_min


def min_cost_action {n : ℕ} (prob : PlanningTask n) (f t : BitVec n) (is_succ : is_successor_state prob f t): Action n :=
    let applicableActs := prob.actions'.filter (fun a => applicable' a f ∧ is_successor' a f t)
    -- TODO ideally use List.minOn in newer mathlib version
    let costs : List ℕ := applicableActs.map (fun x => x.cost)
    let minCost := costs.min (by unfold costs applicableActs ; simp_all)
    let opt_act := applicableActs.find? (·.cost = minCost)
    have is_act : opt_act.isSome = true := by
      unfold opt_act minCost costs
      simp
      apply min_map

    opt_act.get is_act

lemma min_cost_action_in_prob {n : ℕ} (prob : PlanningTask n) (f t : BitVec n) (is_succ : is_successor_state prob f t):
    min_cost_action prob f t is_succ ∈ prob.actions' := by
    unfold min_cost_action
    simp
    apply List.get_find?_mem


def trans_of_STRIPS {n : ℕ} (prob : PlanningTask n) : NatGraph (BitVec n) :=
  let edges : BitVec n → BitVec n → Prop := fun f t => is_successor_state prob f t

  let dg : Digraph (BitVec n) := Digraph.mk edges
  let dg_dec : DecidableRel dg.Adj := by infer_instance
  let cost : (u v : BitVec n) → dg.Adj u v → ℕ := fun f t adj =>
    cost_of prob f t (by unfold is_successor_state ; grind)

  WeightedDiGraph.mk dg cost dg_dec

def trans_of_STRIPS_goals {n : ℕ} (prob : PlanningTask n) : List (BitVec n) :=
  (List.finRange (2^n)).filter (fun s => satisfies' prob.goal' s)

lemma is_successor_state_of_trans_STRIPS_adj {n : ℕ} (prob : PlanningTask n) (s s' : BitVec n) (adj : (trans_of_STRIPS prob).Adj s s') :
    is_successor_state prob s s' := by
  unfold is_successor_state
  unfold trans_of_STRIPS at adj
  simp_all

lemma min_cost_action_creates_successor {n : ℕ} (prob : PlanningTask n) (s s' : BitVec n) (adj : (trans_of_STRIPS prob).Adj s s') :
  Successor (min_cost_action prob s s' (is_successor_state_of_trans_STRIPS_adj prob s s' adj)) (convertState s) (convertState s') := by
  let a := min_cost_action prob s s' (is_successor_state_of_trans_STRIPS_adj prob s s' adj)
  have hmem : (min_cost_action prob s s'
      (is_successor_state_of_trans_STRIPS_adj prob s s' adj)) ∈
      prob.actions'.filter (fun a => applicable' a s ∧ is_successor' a s s') := by
    unfold min_cost_action
    apply List.get_find?_mem
  have hp := List.of_mem_filter hmem
  simp only [decide_eq_true_eq] at hp
  have h_app : applicable' (min_cost_action prob s s'
      (is_successor_state_of_trans_STRIPS_adj prob s s' adj)) s = true := hp.1
  have h_is : is_successor' (min_cost_action prob s s'
      (is_successor_state_of_trans_STRIPS_adj prob s s' adj)) s s' = true := hp.2
  have h_succ : s' = successor' (min_cost_action prob s s'
      (is_successor_state_of_trans_STRIPS_adj prob s s' adj)) s :=
    is_successor'_eq_successor' _ _ _ h_is
  unfold convertState; simp only [Successor]
  refine ⟨?_, ?_⟩
  · unfold applicable' satisfies' at h_app
    simp only [decide_eq_true_eq] at h_app
    intro i hi
    exact h_app i (Action.mem_pre.mp hi)
  · apply Set.ext
    intro i
    change (s'[i.val] = true) ↔ ((s[i.val] = true ∧ i ∉ a.del) ∨ i ∈ a.add)
    rw [h_succ]
    simp [a, successor', VarSet.mem_iff]

def walk_to_strips_path {n : ℕ} (prob : PlanningTask n) {start goal : BitVec n} (walk : WeightedDiGraph.Walk (G:= trans_of_STRIPS prob) start goal) (is_goal : satisfies' prob.goal' goal):
    PlanningTask.Path prob (convertState start) (convertState goal):=
  match eq : walk with
  | .nil => PlanningTask.Path.empty (convertState start)
  | .cons adj walk' => by
    expose_names
    have is_succ : is_successor_state prob start w := by
      apply is_successor_state_of_trans_STRIPS_adj
      exact adj
    let a : Action n := min_cost_action prob start w is_succ
    apply PlanningTask.Path.cons (a := a) (s2 := convertState w)
    · unfold a
      unfold PlanningTask.actions
      simp
      apply min_cost_action_in_prob
    · apply min_cost_action_creates_successor
      exact adj
    · apply walk_to_strips_path
      · exact walk'
      · exact is_goal

lemma convertState_injective {n} : Function.Injective (@convertState n) := by
  intro a b h
  ext i
  unfold convertState at h
  simp_all
  apply Set.ext_iff.mp at h
  expose_names
  specialize h ⟨i,hi⟩
  grind


lemma state_has_bitvec {n : ℕ} (s : State n) [DecidablePred s.Mem] : ∃ s' : BitVec n, convertState s' = s := by
  unfold State at s
  unfold convertState
  let l := (List.finRange n).map (fun x => decide (s.Mem x))
  have l_length : l.length = n := by grind
  let s' := BitVec.ofBoolListLE l
  use s'.cast l_length
  unfold s' l
  apply Set.ext
  intro x
  constructor
  · intro x_in
    simp_all
    rw [BitVec.getElem_ofBoolListLE] at x_in
    simp_all
    exact x_in
  · intro x_in
    simp_all
    rw [BitVec.getElem_ofBoolListLE]
    simp_all
    exact x_in


lemma adj_of_successor {n : ℕ} {a : Action n} (prob : PlanningTask n) {s s' : BitVec n} (succ : Successor a (convertState s) (convertState s')) (ha : a ∈ prob.actions):
  (trans_of_STRIPS prob).Adj s s' := by
  -- Since `a` is applicable and `succ` is a successor, we have `a ∈ prob.actions'` and `s' = successor' a s`.
  have h_app : applicable' a s := by
    unfold applicable';
    unfold satisfies';
    cases succ ; aesop
  have h_succ : s' = successor' a s := by
    obtain ⟨ _, h_succ ⟩ := succ;
    ext i
    simp_all [ Set.ext_iff, convertState, successor' ]
    specialize h_succ ⟨ i, by assumption ⟩ 
    simp_all [VarSet.getElem_toBitVec' ] ;
    grind
  unfold trans_of_STRIPS; simp_all +decide [ PlanningTask.actions ] ;
  exact ⟨ a, ha, h_app, by unfold is_successor'; simp  ⟩


@[instance_reducible]
noncomputable def successor_dec {n : ℕ} (a : Action n) (s s' : State n) (_ : Successor a s s'):
  DecidablePred (Set.Mem s') :=
  fun _ => Classical.propDecidable _

noncomputable def strips_path_to_walk {n : ℕ} (prob : PlanningTask n) {start goal : BitVec n} (path : PlanningTask.Path prob (convertState start) (convertState goal)):
    WeightedDiGraph.Walk (G:= trans_of_STRIPS prob) start goal
  := by
    generalize hs : convertState start = s at path
    generalize hg : convertState goal = g at path
    cases path with
    | empty s =>
        have : start = goal := convertState_injective (hs.trans hg.symm)
        subst this
        exact WeightedDiGraph.Walk.nil
    | cons a s2 ha succ path' =>
      have s2_mem_dec : DecidablePred (Set.Mem s2) := successor_dec a s s2 succ
      have xx := state_has_bitvec s2
      let s2' := Classical.choose xx
      let s2'_eq_s2 := Classical.choose_spec xx
      apply WeightedDiGraph.Walk.cons (w:= s2')
      · apply adj_of_successor
        · rw [← hs] at succ
          rw [← s2'_eq_s2] at succ
          apply succ
        · exact ha
      · rw [← s2'_eq_s2] at path'
        rw [← hg] at path'
        apply strips_path_to_walk (path := path')
termination_by path.length
decreasing_by
  simp
  expose_names
  have f : path'.length < path.length := by
    have e := heq_iff_eq.mp h_2
    rw [e]
    conv =>
      right
      unfold PlanningTask.Path.length
    simp
  grind

noncomputable def last_dec {n : ℕ} (prob : PlanningTask n) (s : BitVec n) (last : State n) (path : PlanningTask.Path prob (convertState s) last) :
    DecidablePred (Set.Mem last) := by
  cases path
  · intro x
    unfold convertState
    by_cases s_i : s[x] = true
    · apply isTrue
      unfold Set.Mem
      exact s_i
    · apply isFalse
      exact s_i
  case cons a s2 ha succ path' =>
    have s2_mem_dec : DecidablePred (Set.Mem s2) := successor_dec a (convertState s) s2 succ
    have xx := state_has_bitvec s2
    let s2' := Classical.choose xx
    let s2'_eq_s2 := Classical.choose_spec xx
    apply last_dec (path:=s2'_eq_s2 ▸ path')
termination_by path.length
decreasing_by
  expose_names
  have f : π.length < path.length := by
    have e := heq_iff_eq.mp h_2
    rw [e]
    conv =>
      right
      unfold PlanningTask.Path.length
    simp
  grind



namespace PlanningTask.Path

/-- The length of a path. -/
def cost {n} {pt : PlanningTask n} {s s'} : PlanningTask.Path pt s s' → ℕ
| PlanningTask.Path.empty _ => 0
| PlanningTask.Path.cons a _ _ _ π => π.cost + a.cost

/-
The cost of a snoc path equals the prefix cost plus the appended action cost.
-/
lemma cost_snoc {n} {pt : PlanningTask n} {a : Action n} {s1 s2 s3 : State n}
    {ha : a ∈ pt.actions} {path : PlanningTask.Path pt s1 s2} {succ : Successor a s2 s3} :
    (PlanningTask.Path.snoc a s2 ha path succ).cost = path.cost + a.cost := by
      unfold snoc;
      cases path <;> simp_all +decide [ PlanningTask.Path.cost ];
      rename_i a' s2' ha' succ' π';
      have h_ind : ∀ {s : State n} (a : Action n) (s1 s2 : State n) (ha : a ∈ pt.actions) (succ : Successor a s1 s2) (π : PlanningTask.Path pt s s1), (snoc a s1 ha π succ).cost = π.cost + a.cost := by
        intro s a s1 s2 ha succ π
        induction π with
        | empty s_1 => exact Eq.symm (Nat.add_zero ((empty s_1).cost.add a.cost))
        | cons => unfold snoc; simp_all +arith [ PlanningTask.Path.cost ]
      rw [ h_ind a s2 s3 ha succ π' ]
      omega
end PlanningTask.Path

/-! ### Helper lemmas for planner optimality -/

/-
PROBLEM
`min_cost_action` achieves the minimum cost, i.e., its cost equals `cost_of`.

PROVIDED SOLUTION
Unfold both `min_cost_action` and `cost_of`. They share the same `applicableActs` and `costs` definitions. `min_cost_action` finds an action via `find?` whose cost equals `costs.min`, and `cost_of` returns `costs.min`. So `min_cost_action.cost = costs.min = cost_of`. The key is that `find?` returns an element satisfying `·.cost = minCost` and `.get` extracts it, so `.cost = minCost`.
-/
lemma min_cost_action_cost_eq_cost_of {n : ℕ} (prob : PlanningTask n) (f t : BitVec n)
    (is_succ : is_successor_state prob f t) :
    (min_cost_action prob f t is_succ).cost = cost_of prob f t is_succ := by
  unfold cost_of min_cost_action at *;
  grind only [List.get_find?_prop]

/-
PROBLEM
The edge cost in `trans_of_STRIPS` equals `cost_of`.

PROVIDED SOLUTION
Unfold `NatGraph.edgeCost` to get `G.Payload f t adj`. Unfold `trans_of_STRIPS` - the Payload is defined as `cost_of prob f t (some_proof)`. By `WeightedDiGraph.Payload_irr`, the proof doesn't matter, so this equals `cost_of prob f t (is_successor_state_of_trans_STRIPS_adj prob f t adj)`.
-/
lemma trans_of_STRIPS_edgeCost {n : ℕ} (prob : PlanningTask n) (f t : BitVec n)
    (adj : (trans_of_STRIPS prob).Adj f t) :
    NatGraph.edgeCost adj = cost_of prob f t (is_successor_state_of_trans_STRIPS_adj prob f t adj) := by
  rfl
lemma cost_of_le_action_cost {n : ℕ} (prob : PlanningTask n) (f t : BitVec n) (a : Action n)
    (is_succ : is_successor_state prob f t)
    (a_in_prob : a ∈ prob.actions')
    (a_applicable : applicable' a f = true) (a_produces : is_successor' a f t = true) :
    cost_of prob f t is_succ ≤ a.cost := by
  have h_a_in_applicableActs : a ∈ prob.actions'.filter (fun a => applicable' a f ∧ is_successor' a f t) := by
    grind;
  apply List.min_le_of_mem;
  exact List.mem_map.mpr ⟨ a, h_a_in_applicableActs, rfl ⟩

/-
PROBLEM
The STRIPS path cost of `walk_to_strips_path` equals the graph walk cost.

PROVIDED SOLUTION
By induction on walk.
- nil case: both costs are 0 (PlanningTask.Path.empty has cost 0, Walk.nil has cost 0).
- cons case: walk = cons adj walk'. walk_to_strips_path produces PlanningTask.Path.cons (min_cost_action ...) ... (walk_to_strips_path walk'). STRIPS cost = (walk_to_strips_path walk').cost + (min_cost_action ...).cost. By IH, (walk_to_strips_path walk').cost = walk'.cost. And (min_cost_action ...).cost = cost_of ... = edgeCost adj (by min_cost_action_cost_eq_cost_of and trans_of_STRIPS_edgeCost). Walk.cost of cons = edgeCost adj + walk'.cost. So STRIPS cost = walk'.cost + edgeCost adj = edgeCost adj + walk'.cost = walk.cost.
-/
lemma walk_to_strips_path_cost_eq {n : ℕ} (prob : PlanningTask n) {start goal : BitVec n}
    (walk : WeightedDiGraph.Walk (G := trans_of_STRIPS prob) start goal)
    (is_goal : satisfies' prob.goal' goal) :
    (walk_to_strips_path prob walk is_goal).cost = walk.cost := by
  revert walk is_goal;
  intro walk;
  induction walk;
  · intro is_goal
    simp_all only [WeightedDiGraph.Walk.cost_nil_zero]
    rfl
  · intro is_goal
    unfold walk_to_strips_path
    unfold PlanningTask.Path.cost WeightedDiGraph.Walk.cost
    rw [ add_comm, min_cost_action_cost_eq_cost_of, trans_of_STRIPS_edgeCost ]
    simp_all

/-
PROBLEM
For any STRIPS plan, there exists a graph walk whose cost is at most the plan's path cost.

If action `a` is in `prob.actions` (Finset), then it's in `prob.actions'` (List).

PROVIDED SOLUTION
Use strips_path_to_walk to get a graph walk, then show its cost ≤ path.cost by induction on the path. Alternatively, construct the walk directly by induction on path:
- empty: use Walk.nil, cost 0 ≤ 0
- cons with action a, successor from s1 to s2, and rest path from s2 to goal:
  - s2 has a BitVec representation s2' (via state_has_bitvec, using successor_dec for decidability)
  - There's a graph edge from start to s2' (by adj_of_successor)
  - edgeCost = cost_of ≤ a.cost (by cost_of_le_action_cost, since a is applicable and produces the transition, and a ∈ prob.actions')
  - By IH on the rest path (from convertState s2' to convertState goal), get walk' with cost ≤ rest.cost
  - Combine: Walk.cons adj walk' with cost = edgeCost + walk'.cost ≤ a.cost + rest.cost = path.cost

Key: need to handle the DecidablePred for s2, use state_has_bitvec and Classical.choose. The function adj_of_successor gives the graph adjacency. cost_of_le_action_cost bounds the edge cost.

Need to handle termination carefully - use path.length as the termination measure, similar to strips_path_to_walk.

PlanningTask.actions is defined as List.toFinset prob.actions'. So a ∈ prob.actions means a ∈ prob.actions'.toFinset, which implies a ∈ prob.actions'. Unfold PlanningTask.actions and use List.mem_toFinset.
-/
lemma mem_actions'_of_mem_actions {n : ℕ} {prob : PlanningTask n} {a : Action n}
    (ha : a ∈ prob.actions) : a ∈ prob.actions' := by
  exact List.mem_dedup.mp ha

/-
If `Successor a (convertState s) (convertState t)` with `a ∈ prob.actions`,
    then `applicable' a s` and `is_successor' a s t`.

-/
lemma successor_implies_applicable {n : ℕ}
    {a : Action n} {s t : BitVec n}
    (succ : Successor a (convertState s) (convertState t)) :
    applicable' a s = true := by
  obtain ⟨h_pre, h_succ⟩ := succ;
  rw [applicable'_iff]; intro i hi; exact h_pre (Action.mem_pre.mpr hi)

lemma successor_implies_is_successor {n : ℕ}
    {a : Action n} {s t : BitVec n}
    (succ : Successor a (convertState s) (convertState t)) :
    is_successor' a s t = true := by
  obtain ⟨h_pre, h_succ⟩ := succ;
  -- Since `convertState` is injective, we can conclude that `t = successor' a s`.
  have h_eq : t = successor' a s := by
    ext i;
    replace h_succ := Set.ext_iff.mp h_succ ⟨ i, by assumption ⟩
    simp_all [successor', VarSet.getElem_toBitVec' ]
    grind
  simp [h_eq, is_successor']


private lemma strips_path_has_cheaper_walk_aux {n : ℕ} (prob : PlanningTask n) (k : ℕ)
    {start goal : BitVec n}
    (path : PlanningTask.Path prob (convertState start) (convertState goal))
    (hlen : path.length ≤ k) :
    ∃ w : WeightedDiGraph.Walk (G := trans_of_STRIPS prob) start goal, w.cost ≤ path.cost := by
  induction k generalizing start goal with
  | zero =>
    generalize hs : convertState start = s at path
    generalize hg : convertState goal = g at path
    cases path with
    | empty =>
      have : start = goal := convertState_injective (hs.trans hg.symm)
      subst this
      exact ⟨WeightedDiGraph.Walk.nil, le_refl 0⟩
    | cons => simp [PlanningTask.Path.length] at hlen
  | succ k ih =>
    generalize hs : convertState start = s at path
    generalize hg : convertState goal = g at path
    cases path with
    | empty =>
      have : start = goal := convertState_injective (hs.trans hg.symm)
      subst this
      exact ⟨WeightedDiGraph.Walk.nil, le_refl 0⟩
    | cons a s2 ha succ path' =>
      subst hs; subst hg
      haveI := successor_dec a (convertState start) s2 succ
      obtain ⟨s2', rfl⟩ := state_has_bitvec s2
      have adj := adj_of_successor prob succ ha
      have path'_len : path'.length ≤ k := by
        simp [PlanningTask.Path.length] at hlen; exact hlen
      obtain ⟨walk', hw'⟩ := ih path' path'_len
      refine ⟨WeightedDiGraph.Walk.cons adj walk', ?_⟩
      have edge_le : NatGraph.edgeCost adj ≤ a.cost := by
        rw [trans_of_STRIPS_edgeCost]
        exact cost_of_le_action_cost prob start s2' a _
          (mem_actions'_of_mem_actions ha)
          (successor_implies_applicable succ)
          (successor_implies_is_successor succ)
      show (WeightedDiGraph.Walk.cons adj walk').cost ≤
        (PlanningTask.Path.cons a (convertState s2') ha succ path').cost
      simp only [WeightedDiGraph.Walk.cost, PlanningTask.Path.cost]
      calc NatGraph.edgeCost adj + walk'.cost
          ≤ a.cost + path'.cost := Nat.add_le_add edge_le hw'
        _ = path'.cost + a.cost := Nat.add_comm _ _

lemma strips_path_has_cheaper_walk {n : ℕ} (prob : PlanningTask n) {start goal : BitVec n}
    (path : PlanningTask.Path prob (convertState start) (convertState goal)) :
    ∃ w : WeightedDiGraph.Walk (G := trans_of_STRIPS prob) start goal, w.cost ≤ path.cost :=
  strips_path_has_cheaper_walk_aux prob path.length path (le_refl _)



lemma satisfies'_implies_GoalState {n : ℕ} (prob : PlanningTask n) (goal : BitVec n)
    (h : satisfies' prob.goal' goal = true) :
    prob.GoalState (convertState goal) := by
  -- Unfold `satisfies'` and `convertState`, then simplify using the definition of `GoalState` in ` PlanningTask`.
  simp [satisfies', convertState, PlanningTask.GoalState] at h ⊢
  intro i hi
  simpa using h i hi

lemma GoalState_implies_satisfies' {n : ℕ} (prob : PlanningTask n) (goal : BitVec n)
    (h : prob.GoalState (convertState goal)) :
    satisfies' prob.goal' goal = true := by
  -- Let's unfold `satisfies'` and the `convertState` membership characterization, then
  -- use the ` PlanningTask.GoalState` hypothesis `h` (subset inclusion) to discharge the goal.
  simp [satisfies', PlanningTask.GoalState, convertState] at h ⊢;
  -- By definition of subset, if i is in the goal set, then goal[i] must be true.
  intros i hi
  apply h
  exact hi

lemma mem_trans_of_STRIPS_goals_iff {n : ℕ} (prob : PlanningTask n) (goal : BitVec n) :
    goal ∈ trans_of_STRIPS_goals prob ↔ satisfies' prob.goal' goal = true := by
  unfold trans_of_STRIPS_goals
  simp
  exact fun _ => ⟨goal.toFin, rfl⟩

lemma PlanningTask.Path.cost_eq_of_cast {n : ℕ} {pt : PlanningTask n} {s s1 s2 : State n}
    (h : s1 = s2) (p : PlanningTask.Path pt s s2) :
    (show PlanningTask.Path pt s s1 from h ▸ p).cost = p.cost := by
  subst h; rfl


def max_action_cost {n : ℕ} (prob : PlanningTask n) : ℕ := if empty : prob.actions'.length = 0 then 1 else
  (prob.actions'.map (·.cost)).max (by rw [ne_eq] ; rw [List.map_eq_nil_iff] ; rw [←List.length_eq_zero_iff];  exact empty)


/-
PROVIDED SOLUTION
First, rewrite the edge cost using trans_of_STRIPS_edgeCost to get cost_of prob f t .... Then cost_of returns List.min of costs of applicable actions. This min ≤ any element in the list. The applicable actions are a subset of prob.actions'. Each action cost ≤ max_action_cost (which is List.max of all action costs, or 1 if empty). Use List.min_le_of_mem and List.le_max_of_mem, or just show cost_of ≤ some particular action's cost ≤ max_action_cost.

Rewrite edgeCost using trans_of_STRIPS_edgeCost. Then we have cost_of prob f t is_succ ≤ max_action_cost prob. Unfold cost_of and max_action_cost. The cost_of is List.min of applicable action costs. List.min is a member of the list (List.min_mem). Each applicable action is in prob.actions', so its cost is in the cost map of prob.actions'. By List.le_max_of_mem, each such cost ≤ List.max of all action costs. The max_action_cost uses if-then-else: if actions' empty then 1 else List.max. Since adj implies there's at least one applicable action, actions' is non-empty, so the if goes to else branch. Use split on the if, in the empty case derive contradiction from adj, in the non-empty case use List.min_le_of_mem and List.le_max_of_mem with transitivity.
-/
private lemma edge_cost_le_max_action_cost {n : ℕ} (prob : PlanningTask n)
    {f t : BitVec n} (adj : (trans_of_STRIPS prob).Adj f t) :
    NatGraph.edgeCost adj ≤ max_action_cost prob := by
      -- Since cost_of returns the minimum cost of applicable actions and max_action_cost is the maximum cost of any action, we have cost_of prob f t ... ≤ max_action_cost prob.
      have h_cost_of_le_max : ∃ a ∈ prob.actions', a.cost = cost_of prob f t (is_successor_state_of_trans_STRIPS_adj prob f t adj) := by
        have h_cost_of_le_max : ∃ a ∈ prob.actions'.filter (fun a => applicable' a f ∧ is_successor' a f t), a.cost = cost_of prob f t (is_successor_state_of_trans_STRIPS_adj prob f t adj) := by
          unfold cost_of; simp only; exact min_map _ _ _
        generalize_proofs at *; (
        exact ⟨ h_cost_of_le_max.choose, List.mem_of_mem_filter h_cost_of_le_max.choose_spec.1, h_cost_of_le_max.choose_spec.2 ⟩)
      obtain ⟨a, ha_mem, ha_cost⟩ := h_cost_of_le_max
      have h_max_ge_a : a.cost ≤ max_action_cost prob := by
        unfold max_action_cost;
        split_ifs <;> simp_all;
        exact List.le_max_of_mem ( List.mem_map.mpr ⟨ a, ha_mem, rfl ⟩ ) |> le_trans ha_cost.ge
      exact le_trans ha_cost.ge h_max_ge_a

/-
PROVIDED SOLUTION
By induction on w. Base case (nil): cost = 0 = 0 * bound. Cons case (cons adj rest): cost = edgeCost adj + rest.cost. By IH, rest.cost ≤ rest.length * bound. By h_edge, edgeCost adj ≤ bound. So cost ≤ bound + rest.length * bound = (1 + rest.length) * bound = w.length * bound.
-/
private lemma walk_cost_le_length_mul_bound {V : Type} [FinEnum V] {G : NatGraph V}
    {u v : V} (w : G.Walk u v) (bound : ℕ)
    (h_edge : ∀ (a b : V) (adj : G.Adj a b), NatGraph.edgeCost adj ≤ bound) :
    w.cost ≤ w.length * bound := by
      induction w;
      · simp [ WeightedDiGraph.Walk.length ];
      · rw [ WeightedDiGraph.Walk.length, WeightedDiGraph.Walk.cost ];
        grind

/-
PROBLEM
A path cannot contain the same node twice. I.e. any path contains at most 2^n - 1 many
actions and its cost is at most 2^n times the maximum action cost.
Modified from the original statement: changed `<` to `≤` because the strict bound fails
when all action costs are zero.

PROVIDED SOLUTION
BitVec n = BitVec n. The FinEnum instance for BitVec n is defined via FinEnum.ofList (List.range (2^n)). Fintype.card for a FinEnum type equals FinEnum.card, which equals the length of FinEnum.toList. For ofList l proof, toList is defined as l.dedup or similar. The list used is List.range (2^n) which already has no duplicates (List.nodup_range). So the length is at most (List.range (2^n)).length = 2^n.
-/
private lemma fintype_card_state'_le (n : ℕ) : Fintype.card (BitVec n) ≤ 2^n := by
  have h : Fintype.card (BitVec n) = Fintype.card (Fin (2^n)) :=
    Fintype.card_congr {
      toFun := BitVec.toFin
      invFun := BitVec.ofFin
      left_inv := fun x => by simp
      right_inv := fun x => by simp
    }
  rw [h, Fintype.card_fin]

lemma all_paths_shorter_than {n : ℕ} (prob : PlanningTask n):
    ∀ goal ∈ trans_of_STRIPS_goals prob, ∀ path : WeightedDiGraph.Path (G:= (trans_of_STRIPS prob)) (state'_of_varset' prob.init') goal, path.cost ≤ (2^n) * (max_action_cost prob) := by
  intro goal _ path
  have h_cost := walk_cost_le_length_mul_bound path.val (max_action_cost prob)
    (fun a b adj => edge_cost_le_max_action_cost prob adj)
  have h_len_lt := path.path_length_lt_card
  calc path.cost = path.val.cost := WeightedDiGraph.Path.cost_same path
    _ ≤ path.val.length * max_action_cost prob := h_cost
    _ ≤ (Fintype.card (BitVec n) - 1) * max_action_cost prob :=
        Nat.mul_le_mul_right _ (Nat.le_sub_one_of_lt h_len_lt)
    _ ≤ Fintype.card (BitVec n) * max_action_cost prob :=
        Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    _ ≤ 2 ^ n * max_action_cost prob :=
        Nat.mul_le_mul_right _ (fintype_card_state'_le n)

/-
If an action produces a goal state from some predecessor, the action is regressable
    through the goal. This follows from the Successor definition: for each deleted variable
    that is in the goal, it must also be added (since it's in the successor despite deletion).
-/
lemma successor_goal_implies_regressable {n : ℕ} (a : Action n)
    (s goal : State n) (g : VarSet n)
    (hsucc : Successor a s goal)
    (hgoal : convertVarSet g ⊆ goal) :
    regressable' a (state'_of_varset' g) = true := by
  obtain ⟨h_pre, h_succ⟩ := hsucc;
  simp [regressable']
  intro i hi; have := hgoal
  simp_all [ Set.subset_def]
  exact Classical.or_iff_not_imp_left.2 fun h => by simpa [ hi ] using hgoal i ( by simpa [ convertVarSet ] using h ) ;

/-
If action a produces a goal state from s_prev, and a is regressable through g,
    then s_prev satisfies the regressed goal.
-/
lemma predecessor_satisfies_regressed_goal {n : ℕ} (a : Action n)
    (s_prev goal : State n) (g : VarSet n)
    (hsucc : Successor a s_prev goal)
    (hgoal : convertVarSet g ⊆ goal) :
    convertVarSet (varset'_of_state' (regress' a (state'_of_varset' g))) ⊆ s_prev := by
  intro i hi
  have hi' : i ∈ varset'_of_state' (regress' a (state'_of_varset' g)) := by
    exact hi
  have hreg : (i ∈ g ∧ i ∉ a.add) ∨ i ∈ a.pre := by
    simpa [varset'_of_state', regress', state'_of_varset', VarSet.mem_iff,
      Action.add, Action.pre] using hi'
  rcases hreg with ⟨hig, hna⟩ | hip
  · have higoal : i ∈ goal := hgoal hig
    rw [hsucc.2] at higoal
    rcases higoal with hidiff | hiadd
    · exact hidiff.1
    · exact False.elim (hna hiadd)
  · exact hsucc.1 hip

/-- Any graph path in the STRIPS transition graph has cost ≤ 2^n * max_action_cost,
    regardless of its start and end states. -/
lemma graph_path_cost_le_bound {n : ℕ} (prob : PlanningTask n) (s g : BitVec n)
    (path : WeightedDiGraph.Path (G := trans_of_STRIPS prob) s g) :
    path.cost ≤ 2 ^ n * max_action_cost prob := by
  have h_cost := walk_cost_le_length_mul_bound path.val (max_action_cost prob)
    (fun a b adj => edge_cost_le_max_action_cost prob adj)
  have h_len_lt := path.path_length_lt_card
  calc path.cost = path.val.cost := WeightedDiGraph.Path.cost_same path
    _ ≤ path.val.length * max_action_cost prob := h_cost
    _ ≤ (Fintype.card (BitVec n) - 1) * max_action_cost prob :=
        Nat.mul_le_mul_right _ (Nat.le_sub_one_of_lt h_len_lt)
    _ ≤ Fintype.card (BitVec n) * max_action_cost prob :=
        Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    _ ≤ 2 ^ n * max_action_cost prob :=
        Nat.mul_le_mul_right _ (fintype_card_state'_le n)
