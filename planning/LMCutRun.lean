import planning.LMCutFast

/-!
# Running LM-cut with a shared precondition-choice function

`STRIPS.lmcut_fast` (see `planning.LMCutFast`) computes the right value, but it is very slow to
*run*, and the reason is a compilation artefact rather than the algorithm:

`h1_pcf_fast p hp` has to *build* a precondition-choice function, and building it costs one
complete `h^max` fixpoint (`h1Values p`).  Its type,
`Π p, has_preconditions p → precondition_choice_function p`, ends in a function type, so the
compiler η-expands the definition to take the action as a further argument.  The consequence is
that `pcf prob hp` is only a *partial application*: nothing is computed when it is formed, and the
whole body — including the `h^max` fixpoint — is re-executed on **every** query `pcf a`.  The
justification graph asks such a query once per (fact, action) pair, so one LM-cut round costs
`Θ(|facts| · |actions|)` `h^max` fixpoints instead of one.

The fix is to hand back the choice function inside a one-field structure (`PcfBox`).  A definition
whose type is a structure is not η-expanded, so `pcf prob hp` really runs the body once, and the
closure stored in the box is shared by every query.

This file therefore duplicates the LM-cut recursion with a boxed precondition-choice function
(`lmcut_inner_box`, `lmcut_box`), proves that it computes exactly the same thing
(`lmcut_inner_box_eq`, `lmcut_box_eq`), and installs the resulting implementation of
`STRIPS.lmcut_fast` with `@[csimp]` (`lmcut_fast_eq_run`).  No statement changes: everything that
is known about `lmcut_fast` (in particular `lmcut_fast_eq` and admissibility) is untouched.
-/

namespace STRIPS

variable {n : ℕ}

/-- A precondition-choice function wrapped in a structure.

The wrapper exists for one reason: a definition returning a `PcfBox` is not η-expanded by the
compiler, so the (expensive) work of building the choice function is done once, when the box is
built, and not again on every query. -/
structure PcfBox {n : ℕ} (p : PlanningTask n) where
  /-- The choice function stored in the box. -/
  fn : precondition_choice_function p
  /-- The chosen precondition of every action of `p`, in the order of `p.actions'`.  The table is
  built together with the choice function, from data the builder has anyway, so that a caller
  that needs the choice of *every* action (the buckets of the justification graph) does not have
  to query the closure once per action. -/
  tbl : List (Fin n)
  /-- `tbl` really lists the choices of `fn`. -/
  htbl : tbl = p.actions'.attach.map (fun a => (↑(fn a) : Fin n))

/-! ### Bucketing with a table of keys

`bucketsOfList` evaluates the key function once per element.  When the keys are known already —
as they are for the buckets of the justification graph, whose keys are the entries of
`PcfBox.tbl` — the same buckets are obtained without evaluating the key function at all. -/

/-- Distribute a list into `n` buckets according to a list of keys given in parallel to it,
keeping the order of the list. -/
def bucketsOfKeys {n : ℕ} {α : Type} : List (Fin n) → List α → _root_.Vector (List α) n
  | k :: ks, a :: as => let acc := bucketsOfKeys ks as; acc.set k (a :: acc[k])
  | _, _ => Vector.replicate n []

/-- Run with the real keys, `bucketsOfKeys` is `bucketsOfList`. -/
theorem bucketsOfKeys_eq {n : ℕ} {α : Type} (key : α → Fin n) :
    ∀ (l : List α) (keys : List (Fin n)), keys = l.map key →
      bucketsOfKeys keys l = bucketsOfList key l := by
  intro l
  induction l with
  | nil => intro keys hk; subst hk; rfl
  | cons a as ih =>
      intro keys hk
      subst hk
      simp only [List.map_cons]
      rw [bucketsOfKeys, bucketsOfList, List.foldr_cons, ih (as.map key) rfl, bucketsOfList]

/-- The buckets of the justification graph, read off the table of a boxed choice function: no
query of the choice function at all. -/
def jgBucketsOfBox {n : ℕ} (prob : PlanningTask n) (box : PcfBox prob) :
    _root_.Vector (List {b : Action n // b ∈ prob.actions'}) n :=
  bucketsOfKeys box.tbl prob.actions'.attach

/-- The buckets read off the table are the buckets. -/
theorem jgBucketsOfBox_eq {n : ℕ} (prob : PlanningTask n) (box : PcfBox prob) :
    jgBucketsOfBox prob box = jgBuckets prob box.fn := by
  rw [jgBucketsOfBox, bucketsOfKeys_eq _ _ _ box.htbl,
    congrFun (congrFun (congrFun jgBuckets_eq_fast n) prob) box.fn, jgBucketsFast]

/-- The plain precondition-choice function family underlying a boxed one. -/
def PcfBox.unbox {n : ℕ} (pcf : Π p : PlanningTask n, has_preconditions p → PcfBox p) :
    Π p : PlanningTask n, has_preconditions p → precondition_choice_function p :=
  fun p hp => (pcf p hp).fn

/-- `lmcut_step` with the goal zone passed in, so that a caller that has the goal zone already
(for the zero-cost-reachability test) does not compute it a second time. -/
def lmcut_step_gz {n : ℕ} (prob : PlanningTask n)
    (pcf : precondition_choice_function prob) (gz : List (Fin n)) :
      (List (Action n)) × ℕ × (cost_partitioning prob 2) :=
  lmcut_step_of prob pcf
    (landmark_induced_by_cut prob (cut_entering (justification_graph prob pcf) gz) pcf)

/-- Run with the real goal zone, `lmcut_step_gz` is `lmcut_step`. -/
theorem lmcut_step_gz_eq {n : ℕ} (prob : PlanningTask n) (u_g : unitary_goal prob)
    (pcf : precondition_choice_function prob) :
    lmcut_step_gz prob pcf
        (goal_zone (justification_graph prob pcf) (get_unitary_goal prob u_g))
      = lmcut_step prob u_g pcf := rfl

/-! ### Sharing the buckets of a round

A round of the recursion builds the justification graph three times: once for the
reachability tests, once inside `lmcut_step_gz` for the cut, and once more, implicitly, when
the landmark induced by the cut is collected by a scan over all actions.  Each of those
evaluates the precondition-choice function once per action, which is the most expensive part
of a round.

The following computes the buckets of the graph (`jgBuckets`, one choice-function query per
action) *once* and reads the graph, the cut and the landmark off them. -/

/-- The landmark induced by a cut, read off the buckets of the justification graph instead of
by a scan over all actions for every cut edge. -/
def landmark_ofBuckets {n : ℕ} {prob : PlanningTask n}
    (bs : _root_.Vector (List {b : Action n // b ∈ prob.actions'}) n)
    (cut : List (Fin n × Fin n)) : List (Action n) :=
  cut.flatMap (fun ft => (bs[ft.1].filter (fun a => decide (ft.2 ∈ a.val.add))).map (·.val))

/-- Read off the real buckets, `landmark_ofBuckets` is `landmark_induced_by_cut`. -/
theorem landmark_ofBuckets_eq {n : ℕ} (prob : PlanningTask n)
    (pcf : precondition_choice_function prob) (cut : List (Fin n × Fin n)) :
    landmark_ofBuckets (jgBuckets prob pcf) cut = landmark_induced_by_cut prob cut pcf := by
  rw [landmark_ofBuckets, landmark_induced_by_cut]
  apply List.flatMap_congr
  intro ft _
  obtain ⟨f, t⟩ := ft
  rw [jgBuckets_filter_eq prob pcf f t]

/-- `lmcut_step`, with the buckets and the justification graph of the round passed in: the cut
is taken from the graph and the landmark is read off the buckets, so neither is recomputed. -/
def lmcut_step_jg {n : ℕ} (prob : PlanningTask n)
    (pcf : precondition_choice_function prob)
    (bs : _root_.Vector (List {b : Action n // b ∈ prob.actions'}) n)
    (jg : NatGraph (Fin n)) (gz : List (Fin n)) :
      (List (Action n)) × ℕ × (cost_partitioning prob 2) :=
  lmcut_step_of prob pcf (landmark_ofBuckets bs (cut_entering jg gz))

/-- Run with the real buckets and the real justification graph, `lmcut_step_jg` is
`lmcut_step_gz`. -/
theorem lmcut_step_jg_eq {n : ℕ} (prob : PlanningTask n)
    (pcf : precondition_choice_function prob) (gz : List (Fin n)) :
    lmcut_step_jg prob pcf (jgBuckets prob pcf) (justification_graph prob pcf) gz
      = lmcut_step_gz prob pcf gz := by
  rw [lmcut_step_jg, lmcut_step_gz, landmark_ofBuckets_eq]

/-- The justification graph built from buckets that are computed once is the justification
graph. -/
theorem justification_graph_ofBuckets_eq {n : ℕ} (prob : PlanningTask n)
    (pcf : precondition_choice_function prob) :
    justification_graph_ofBuckets prob pcf (jgBuckets prob pcf) rfl
      = justification_graph prob pcf :=
  (congrFun (congrFun (congrFun justification_graph_eq_fast n) prob) pcf).symm

/-- `lmcut_inner` with a boxed precondition-choice function; see `lmcut_inner_box_eq`. -/
def lmcut_inner_box {n : ℕ} (prob : PlanningTask n)
    (u_i : unitary_init prob)
    (u_g : unitary_goal prob)
    (hp : has_preconditions prob)
    (pcf : Π p : PlanningTask n, has_preconditions p → PcfBox p) :
      List (List (Action n)) × ℕ∞ × Σ p : ℕ, (cost_partitioning prob p) :=
    let pcf0 := (pcf prob hp).fn
    let jg := justification_graph prob pcf0
    let i := (get_unitary_init prob u_i)
    let goal := (get_unitary_goal prob u_g)
    let gz := goal_zone jg goal

    if ¬ reachable jg i goal then ([[]], ⊤ , ⟨0, fun p => p.elim0⟩)
    else if i ∈ gz then ([], 0, ⟨0, fun p => p.elim0⟩)
    else
     let r := lmcut_step_gz prob pcf0 gz
     let subprob := partition_STRIPS prob r.2.2 ⟨1, by omega⟩

     let subret := lmcut_inner_box subprob u_i u_g
       (partition_STRIPS_has_preconditions prob r.2.2 ⟨1, by omega⟩ hp) pcf

     let lms : List (List (Action n)):= r.1 :: subret.1
     let hval : ℕ∞ := (r.2.1 : ℕ∞) + subret.2.1
     let parts : Σ p : ℕ, (cost_partitioning prob p) :=
       ⟨1 + subret.2.2.1, fun p a =>
         if h : (p : ℕ) = 0 then r.2.2 0 a
         else subret.2.2.2 ⟨(p : ℕ) - 1, by have := p.isLt; omega⟩
           (Fin.cast (partition_STRIPS_actions_length prob r.2.2 ⟨1, by omega⟩).symm a)⟩
     (lms, hval, parts)

termination_by (prob.actions'.map (fun a => a.cost)).sum
decreasing_by
  all_goals (
    rw [lmcut_step_gz_eq prob u_g (pcf prob hp).fn]
    apply lmcut_step_subprob_sum_lt prob u_g (pcf prob hp).fn
    apply lmcut_step_yields_non_zero_heuristic prob u_i u_g (pcf prob hp).fn
    · exact not_not.mp (by assumption)
    · intro hz
      exact (by assumption : ¬ (get_unitary_init prob u_i ∈
        goal_zone (justification_graph prob (pcf prob hp).fn) (get_unitary_goal prob u_g)))
        ((mem_goal_zone_iff _ _ _).mpr hz))

/-- The boxed recursion computes exactly what the original one computes. -/
theorem lmcut_inner_box_eq_aux {n : ℕ}
    (pcf : Π p : PlanningTask n, has_preconditions p → PcfBox p) (M : ℕ) :
    ∀ (prob : PlanningTask n) (u_i : unitary_init prob) (u_g : unitary_goal prob)
      (hp : has_preconditions prob),
      (prob.actions'.map (fun a => a.cost)).sum = M →
      lmcut_inner_box prob u_i u_g hp pcf
        = lmcut_inner prob u_i u_g hp (PcfBox.unbox pcf) := by
  induction' M using Nat.strong_induction_on with M ih
  intro prob u_i u_g hp hM
  rw [lmcut_inner_box, lmcut_inner]
  simp only [PcfBox.unbox, mem_goal_zone_iff]
  split_ifs with h1 h2
  · rfl
  · have hlt : ((partition_STRIPS prob (lmcut_step prob u_g (pcf prob hp).fn).2.2
        ⟨1, by omega⟩).actions'.map (fun a => a.cost)).sum < M := by
      subst hM
      exact lmcut_step_subprob_sum_lt prob u_g (pcf prob hp).fn
        (lmcut_step_yields_non_zero_heuristic prob u_i u_g (pcf prob hp).fn h1 h2)
    exact congrArg
      (fun subret : List (List (Action n)) × ℕ∞ ×
          Σ p : ℕ, cost_partitioning (partition_STRIPS prob
            (lmcut_step prob u_g (pcf prob hp).fn).2.2 ⟨1, by omega⟩) p =>
        ((lmcut_step prob u_g (pcf prob hp).fn).1 :: subret.1,
          ((lmcut_step prob u_g (pcf prob hp).fn).2.1 : ℕ∞) + subret.2.1,
          (⟨1 + subret.2.2.1, fun p a =>
            if h : (p : ℕ) = 0 then (lmcut_step prob u_g (pcf prob hp).fn).2.2 0 a
            else subret.2.2.2 ⟨(p : ℕ) - 1, by have := p.isLt; omega⟩
              (Fin.cast (partition_STRIPS_actions_length prob
                (lmcut_step prob u_g (pcf prob hp).fn).2.2 ⟨1, by omega⟩).symm a)⟩ :
            Σ p : ℕ, cost_partitioning prob p)))
      (ih _ hlt (partition_STRIPS prob (lmcut_step prob u_g (pcf prob hp).fn).2.2
        ⟨1, by omega⟩) u_i u_g
        (partition_STRIPS_has_preconditions prob _ ⟨1, by omega⟩ hp) rfl)
  · rfl

/-- **The boxed recursion is the original one.** -/
theorem lmcut_inner_box_eq {n : ℕ} (prob : PlanningTask n) (u_i : unitary_init prob)
    (u_g : unitary_goal prob) (hp : has_preconditions prob)
    (pcf : Π p : PlanningTask n, has_preconditions p → PcfBox p) :
    lmcut_inner_box prob u_i u_g hp pcf = lmcut_inner prob u_i u_g hp (PcfBox.unbox pcf) :=
  lmcut_inner_box_eq_aux pcf _ prob u_i u_g hp rfl

/-! ### Reusing the static action data across rounds

The precondition-choice function of a round is built from a complete `h^max` fixpoint, and that
fixpoint starts by extracting, for every action, its precondition list, its add list and its cost
(`h1Data`, one bit-vector scan per list).  The rounds differ only in the *costs* of the actions —
`partition_STRIPS` keeps the names, the preconditions and the add and delete effects
(`partition_STRIPS_getElem_fields`) — so the two lists are extracted over and over again.

The recursion below therefore carries the action data of the current round, together with the
proof that it is the data of the current task, and hands the data of the subproblem to the next
round: `h1DataPartition` only relabels the costs and shares the two lists.  The precondition-choice
function becomes a function of that data (`PcfData`); `PcfData.unbox` instantiates it with the
real data, which is what the equality proofs compare against. -/

/-- `h1Values`, computed from action data supplied by the caller. -/
def h1ValuesOf (p : PlanningTask n) (d : List (H1Action n)) (hd : d = h1Data p) : Vector ℕ n :=
  let v := h1IterFixFast p d hd (h_1_base n p.init'.toBitVec)
  let unreach := Vector.maxFinite v + 1
  v.map (fun x => x.getD unreach)

/-- Run with the real data, `h1ValuesOf` is `h1Values`. -/
theorem h1ValuesOf_eq (p : PlanningTask n) (d : List (H1Action n)) (hd : d = h1Data p) :
    h1ValuesOf p d hd = h1Values p := by
  subst hd; rfl

/-- There is one entry of action data per action. -/
lemma h1Data_length (prob : PlanningTask n) : (h1Data prob).length = prob.actions'.length := by
  simp [h1Data]

/-- The action data of a subproblem of the cost partitioning, from the data of the problem: the
precondition and add lists are shared, only the costs are relabelled. -/
def h1DataPartition {P : ℕ} (prob : PlanningTask n) (part : cost_partitioning prob P) (p : Fin P)
    (d : List (H1Action n)) (hd : d = h1Data prob) : List (H1Action n) :=
  d.mapFinIdx (fun i x h => ⟨x.pre, x.add, part p ⟨i, by
    subst hd; rwa [h1Data_length] at h⟩⟩)

/-- Relabelling the costs really produces the action data of the subproblem. -/
theorem h1DataPartition_eq {P : ℕ} (prob : PlanningTask n) (part : cost_partitioning prob P)
    (p : Fin P) (d : List (H1Action n)) (hd : d = h1Data prob) :
    h1DataPartition prob part p d hd = h1Data (partition_STRIPS prob part p) := by
  subst hd
  have hlen : (h1Data (partition_STRIPS prob part p)).length = (h1Data prob).length := by
    rw [h1Data_length, h1Data_length, partition_STRIPS_actions_length]
  refine List.ext_getElem (by simpa [h1DataPartition] using hlen.symm) ?_
  intro i h1 h2
  have hi : i < prob.actions'.length := by
    rw [h1DataPartition, List.length_mapFinIdx, h1Data_length] at h1; exact h1
  have hi' : i < (partition_STRIPS prob part p).actions'.length := by
    rwa [partition_STRIPS_actions_length]
  have hf := partition_STRIPS_getElem_fields prob part p i hi' hi
  have hc := partition_STRIPS_getElem_cost prob part p i hi' hi
  simp only [h1DataPartition, List.getElem_mapFinIdx, h1Data, List.getElem_map, hf.1, hf.2.1, hc]

/-- A boxed precondition-choice function that is built from action data supplied by the caller. -/
abbrev PcfData (n : ℕ) :=
  Π (p : PlanningTask n) (_ : has_preconditions p) (d : List (H1Action n)), d = h1Data p →
    PcfBox p

/-- The boxed family underlying a data-parameterised one: the data is the real data. -/
def PcfData.unbox (pcf : PcfData n) : Π p : PlanningTask n, has_preconditions p → PcfBox p :=
  fun p hp => pcf p hp (h1Data p) rfl

/-- The data of one round of the recursion: the buckets of the justification graph, the graph
itself and the reachability test, together with the proofs that identify them.  Bundling them
is what makes the buckets be computed **once**: they are built by `mkJGData`, the out-neighbour
bit vectors and the graph are read off them, and the reachability closure is run on the bit
vectors. -/
structure JGData {n : ℕ} (prob : PlanningTask n) (pcf : precondition_choice_function prob)
    (i goal : Fin n) where
  /-- The actions of `prob`, bucketed by their chosen precondition. -/
  bs : _root_.Vector (List {b : Action n // b ∈ prob.actions'}) n
  /-- `bs` really is `jgBuckets`. -/
  hbs : bs = jgBuckets prob pcf
  /-- The justification graph. -/
  jg : NatGraph (Fin n)
  /-- `jg` really is the justification graph. -/
  hjg : jg = justification_graph prob pcf
  /-- Whether `goal` is reachable from `i` in the justification graph. -/
  reach : Bool
  /-- `reach` really is that reachability test. -/
  hreach : reach = reachable jg i goal

/-- The round data, with one pass over the actions: the buckets are read off the table of the
box (so the choice function is not queried at all), the out-neighbour bit vectors are read off
the buckets, the graph is built from both, and the reachability test is run with the bit vectors
(one intersection per vertex and round instead of one bit test per pair of vertices). -/
def mkJGData {n : ℕ} (prob : PlanningTask n) (box : PcfBox prob)
    (i goal : Fin n) : JGData prob box.fn i goal :=
  let bs := jgBucketsOfBox prob box
  let hbs : bs = jgBuckets prob box.fn := jgBucketsOfBox_eq prob box
  let av := jgAddOfBuckets bs
  let hav : av = jgAdd prob box.fn := by
    show jgAddOfBuckets (jgBucketsOfBox prob box) = jgAdd prob box.fn
    rw [jgBucketsOfBox_eq, jgAdd_eq_ofBuckets]
  let jg := justification_graph_of prob box.fn bs av hbs hav
  ⟨bs, hbs, jg, justification_graph_of_eq prob box.fn bs av hbs hav,
    reachableAdj jg av (jgAdd_edgeB prob box.fn bs av hbs hav) i goal,
    reachableAdj_eq jg av (jgAdd_edgeB prob box.fn bs av hbs hav) i goal⟩

/-- `lmcut_inner_box` with the data of a round computed once: the buckets of the justification
graph are built by a single pass over the actions, and the graph, the goal zone, the cut and the
landmark are all read off them; the static action data (`d`) is relabelled instead of being
re-extracted.  See `lmcut_inner_sh_eq`. -/
def lmcut_inner_sh {n : ℕ} (prob : PlanningTask n)
    (u_i : unitary_init prob)
    (u_g : unitary_goal prob)
    (hp : has_preconditions prob)
    (pcf : PcfData n)
    (d : List (H1Action n)) (hd : d = h1Data prob)
    (jd : JGData prob (pcf prob hp d hd).fn (get_unitary_init prob u_i)
      (get_unitary_goal prob u_g)) :
      List (List (Action n)) × ℕ∞ × Σ p : ℕ, (cost_partitioning prob p) :=
    let i := (get_unitary_init prob u_i)
    let goal := (get_unitary_goal prob u_g)
    let gz := goal_zone jd.jg goal

    if ¬ jd.reach then ([[]], ⊤ , ⟨0, fun p => p.elim0⟩)
    else if i ∈ gz then ([], 0, ⟨0, fun p => p.elim0⟩)
    else
     let r := lmcut_step_jg prob (pcf prob hp d hd).fn jd.bs jd.jg gz
     let subprob := partition_STRIPS prob r.2.2 ⟨1, by omega⟩
     let hsub := partition_STRIPS_has_preconditions prob r.2.2 ⟨1, by omega⟩ hp
     let dsub := h1DataPartition prob r.2.2 ⟨1, by omega⟩ d hd
     let hdsub := h1DataPartition_eq prob r.2.2 ⟨1, by omega⟩ d hd

     let subret := lmcut_inner_sh subprob u_i u_g hsub pcf dsub hdsub
       (mkJGData subprob (pcf subprob hsub dsub hdsub) (get_unitary_init subprob u_i)
         (get_unitary_goal subprob u_g))

     let lms : List (List (Action n)):= r.1 :: subret.1
     let hval : ℕ∞ := (r.2.1 : ℕ∞) + subret.2.1
     let parts : Σ p : ℕ, (cost_partitioning prob p) :=
       ⟨1 + subret.2.2.1, fun p a =>
         if h : (p : ℕ) = 0 then r.2.2 0 a
         else subret.2.2.2 ⟨(p : ℕ) - 1, by have := p.isLt; omega⟩
           (Fin.cast (partition_STRIPS_actions_length prob r.2.2 ⟨1, by omega⟩).symm a)⟩
     (lms, hval, parts)

termination_by (prob.actions'.map (fun a => a.cost)).sum
decreasing_by
  all_goals (
    obtain ⟨bs, hbs, jg, hjg, reach, hreach⟩ := jd
    subst hbs
    subst hjg
    subst hreach
    rw [lmcut_step_jg_eq, lmcut_step_gz_eq]
    apply lmcut_step_subprob_sum_lt prob u_g (pcf prob hp d hd).fn
    apply lmcut_step_yields_non_zero_heuristic prob u_i u_g (pcf prob hp d hd).fn
    · exact not_not.mp (by assumption)
    · intro hz
      exact (by assumption : ¬ (get_unitary_init prob u_i ∈
        goal_zone (justification_graph prob (pcf prob hp d hd).fn) (get_unitary_goal prob u_g)))
        ((mem_goal_zone_iff _ _ _).mpr hz))

set_option maxHeartbeats 1000000 in
/-- The recursion with the shared round data computes what the boxed recursion computes. -/
theorem lmcut_inner_sh_eq_aux {n : ℕ} (pcf : PcfData n) (M : ℕ) :
    ∀ (prob : PlanningTask n) (u_i : unitary_init prob) (u_g : unitary_goal prob)
      (hp : has_preconditions prob) (d : List (H1Action n)) (hd : d = h1Data prob)
      (jd : JGData prob (pcf prob hp d hd).fn (get_unitary_init prob u_i)
        (get_unitary_goal prob u_g)),
      (prob.actions'.map (fun a => a.cost)).sum = M →
      lmcut_inner_sh prob u_i u_g hp pcf d hd jd
        = lmcut_inner_box prob u_i u_g hp (PcfData.unbox pcf) := by
  induction' M using Nat.strong_induction_on with M ih
  intro prob u_i u_g hp d hd jd hM
  subst hd
  obtain ⟨bs, hbs, jg, hjg, reach, hreach⟩ := jd
  subst hbs
  subst hjg
  subst hreach
  rw [lmcut_inner_sh, lmcut_inner_box]
  simp only [PcfData.unbox]
  by_cases h1 : ¬ reachable (justification_graph prob (pcf prob hp (h1Data prob) rfl).fn)
      (get_unitary_init prob u_i) (get_unitary_goal prob u_g)
  · rw [if_pos h1, if_pos h1]
  rw [if_neg h1, if_neg h1]
  by_cases h2 : get_unitary_init prob u_i ∈
      goal_zone (justification_graph prob (pcf prob hp (h1Data prob) rfl).fn)
        (get_unitary_goal prob u_g)
  · rw [if_pos h2, if_pos h2]
  rw [if_neg h2, if_neg h2]
  rw [not_not] at h1
  rw [mem_goal_zone_iff] at h2
  -- the two rounds agree: the shared step is the step of the boxed recursion
  have hr : lmcut_step_jg prob (pcf prob hp (h1Data prob) rfl).fn
        (jgBuckets prob (pcf prob hp (h1Data prob) rfl).fn)
        (justification_graph prob (pcf prob hp (h1Data prob) rfl).fn)
        (goal_zone (justification_graph prob (pcf prob hp (h1Data prob) rfl).fn)
          (get_unitary_goal prob u_g))
      = lmcut_step_gz prob (pcf prob hp (h1Data prob) rfl).fn
        (goal_zone (justification_graph prob (pcf prob hp (h1Data prob) rfl).fn)
          (get_unitary_goal prob u_g)) :=
    lmcut_step_jg_eq _ _ _
  have hstep : lmcut_step_gz prob (pcf prob hp (h1Data prob) rfl).fn
        (goal_zone (justification_graph prob (pcf prob hp (h1Data prob) rfl).fn)
          (get_unitary_goal prob u_g))
      = lmcut_step prob u_g (pcf prob hp (h1Data prob) rfl).fn :=
    lmcut_step_gz_eq prob u_g (pcf prob hp (h1Data prob) rfl).fn
  have hlt : ((partition_STRIPS prob (lmcut_step prob u_g (pcf prob hp (h1Data prob) rfl).fn).2.2
      ⟨1, by omega⟩).actions'.map (fun a => a.cost)).sum < M := by
    subst hM
    exact lmcut_step_subprob_sum_lt prob u_g (pcf prob hp (h1Data prob) rfl).fn
      (lmcut_step_yields_non_zero_heuristic prob u_i u_g (pcf prob hp (h1Data prob) rfl).fn h1 h2)
  -- first move to the same round result, then use the induction hypothesis on the subproblem
  refine Eq.trans (congrArg (fun r : List (Action n) × ℕ × cost_partitioning prob 2 =>
      let subprob := partition_STRIPS prob r.2.2 ⟨1, by omega⟩
      let hsub := partition_STRIPS_has_preconditions prob r.2.2 ⟨1, by omega⟩ hp
      let dsub := h1DataPartition prob r.2.2 ⟨1, by omega⟩ (h1Data prob) rfl
      let hdsub := h1DataPartition_eq prob r.2.2 ⟨1, by omega⟩ (h1Data prob) rfl
      let subret := lmcut_inner_sh subprob u_i u_g hsub pcf dsub hdsub
        (mkJGData subprob (pcf subprob hsub dsub hdsub) (get_unitary_init subprob u_i)
          (get_unitary_goal subprob u_g))
      (r.1 :: subret.1, (r.2.1 : ℕ∞) + subret.2.1,
        (⟨1 + subret.2.2.1, fun p a =>
          if h : (p : ℕ) = 0 then r.2.2 0 a
          else subret.2.2.2 ⟨(p : ℕ) - 1, by have := p.isLt; omega⟩
            (Fin.cast (partition_STRIPS_actions_length prob r.2.2 ⟨1, by omega⟩).symm a)⟩ :
          Σ p : ℕ, cost_partitioning prob p))) (hr.trans hstep)) ?_
  exact congrArg
    (fun subret : List (List (Action n)) × ℕ∞ ×
        Σ p : ℕ, cost_partitioning (partition_STRIPS prob
          (lmcut_step prob u_g (pcf prob hp (h1Data prob) rfl).fn).2.2 ⟨1, by omega⟩) p =>
      ((lmcut_step prob u_g (pcf prob hp (h1Data prob) rfl).fn).1 :: subret.1,
        ((lmcut_step prob u_g (pcf prob hp (h1Data prob) rfl).fn).2.1 : ℕ∞) + subret.2.1,
        (⟨1 + subret.2.2.1, fun p a =>
          if h : (p : ℕ) = 0 then (lmcut_step prob u_g (pcf prob hp (h1Data prob) rfl).fn).2.2 0 a
          else subret.2.2.2 ⟨(p : ℕ) - 1, by have := p.isLt; omega⟩
            (Fin.cast (partition_STRIPS_actions_length prob
              (lmcut_step prob u_g (pcf prob hp (h1Data prob) rfl).fn).2.2 ⟨1, by omega⟩).symm a)⟩ :
          Σ p : ℕ, cost_partitioning prob p)))
    (ih _ hlt (partition_STRIPS prob (lmcut_step prob u_g (pcf prob hp (h1Data prob) rfl).fn).2.2
      ⟨1, by omega⟩) u_i u_g
      (partition_STRIPS_has_preconditions prob _ ⟨1, by omega⟩ hp) _ _ _ rfl)

/-- **The recursion with the shared round data is the boxed recursion.** -/
theorem lmcut_inner_sh_eq {n : ℕ} (prob : PlanningTask n) (u_i : unitary_init prob)
    (u_g : unitary_goal prob) (hp : has_preconditions prob) (pcf : PcfData n)
    (d : List (H1Action n)) (hd : d = h1Data prob)
    (jd : JGData prob (pcf prob hp d hd).fn (get_unitary_init prob u_i)
      (get_unitary_goal prob u_g)) :
    lmcut_inner_sh prob u_i u_g hp pcf d hd jd
      = lmcut_inner_box prob u_i u_g hp (PcfData.unbox pcf) :=
  lmcut_inner_sh_eq_aux pcf _ prob u_i u_g hp d hd jd rfl

/-- `lmcut` with a boxed precondition-choice function; see `lmcut_box_eq`. -/
def lmcut_box {n : ℕ} (prob : PlanningTask n) (s : BitVec n)
    (pcf : Π p : PlanningTask (n + 2), has_preconditions p → PcfBox p) : ℕ∞ :=
  if hg : prob.goal'.toList = [] then 0
  else
    (lmcut_inner_box (i_g_normal_form (set_init prob s))
      (i_g_normalform_is_unitary_init _) (i_g_normalform_is_unitary_goal _)
      (i_g_normal_form_has_preconditions (set_init prob s) hg) pcf).2.1

/-- **The boxed LM-cut heuristic is the original one.** -/
theorem lmcut_box_eq {n : ℕ} (prob : PlanningTask n) (s : BitVec n)
    (pcf : Π p : PlanningTask (n + 2), has_preconditions p → PcfBox p) :
    lmcut_box prob s pcf = lmcut prob s (PcfBox.unbox pcf) := by
  rw [lmcut_box, lmcut]
  split_ifs with hg
  · rfl
  · rw [lmcut_inner_box_eq]

/-- `lmcut_box` with the data of each round shared; see `lmcut_box_sh_eq`. -/
def lmcut_box_sh {n : ℕ} (prob : PlanningTask n) (s : BitVec n) (pcf : PcfData (n + 2)) : ℕ∞ :=
  if hg : prob.goal'.toList = [] then 0
  else
    (lmcut_inner_sh (i_g_normal_form (set_init prob s))
      (i_g_normalform_is_unitary_init _) (i_g_normalform_is_unitary_goal _)
      (i_g_normal_form_has_preconditions (set_init prob s) hg) pcf
      (h1Data (i_g_normal_form (set_init prob s))) rfl
      (mkJGData _ (pcf (i_g_normal_form (set_init prob s))
        (i_g_normal_form_has_preconditions (set_init prob s) hg) _ rfl) _ _)).2.1

/-- **Sharing the round data does not change the value.** -/
theorem lmcut_box_sh_eq {n : ℕ} (prob : PlanningTask n) (s : BitVec n) (pcf : PcfData (n + 2)) :
    lmcut_box_sh prob s pcf = lmcut_box prob s (PcfData.unbox pcf) := by
  rw [lmcut_box_sh, lmcut_box]
  split_ifs with hg
  · rfl
  · rw [lmcut_inner_sh_eq]

/-! ### The table of chosen preconditions

The `h_1`-maximiser chooses, for every action, the precondition of maximal `h^max` value.  Its
query enumerates the precondition bit vector of the action (a bit scan) and takes an `argmax`.
The action data `d` carries the precondition *lists* already, so the whole table can be built
from `d`, and then the choice function is never queried per action again. -/

/-- The chosen precondition of every action, computed from the action data: one `argmax` per
action over the precondition list the data carries. -/
def pcfTable (vals : Vector ℕ (n + 2)) (d : List (H1Action (n + 2))) : List (Fin (n + 2)) :=
  d.map (fun da => (da.pre.argmax (fun i => vals[i])).getD ⟨0, by omega⟩)

/-- Run with the real action data, `pcfTable` lists the choices of `h1_pcf_of`. -/
theorem pcfTable_eq (p : PlanningTask (n + 2)) (hp : has_preconditions p)
    (vals : Vector ℕ (n + 2)) (d : List (H1Action (n + 2))) (hd : d = h1Data p) :
    pcfTable vals d = p.actions'.attach.map (fun a => (↑(h1_pcf_of p hp vals a) : Fin (n + 2))) := by
  subst hd
  rw [pcfTable, h1Data, List.map_map]
  refine List.ext_getElem (by simp) ?_
  intro i h1 h2
  have hi : i < p.actions'.length := by simpa using h1
  simp only [List.getElem_map]
  have hattach : (p.actions'.attach)[i]'(by simpa using h2) =
      ⟨p.actions'[i]'hi, by simp⟩ := by
    simp
  rw [hattach]
  exact (Option.get_eq_getD _).symm

/-- The `h_1`-maximiser precondition-choice function, in a box: the `h^max` fixpoint is computed
when the box is built, and the closure it produces is shared by every query. -/
def h1_pcf_box : Π p : PlanningTask (n + 2), has_preconditions p → PcfBox p :=
  fun p hp => ⟨h1_pcf_of p hp (h1Values p), pcfTable (h1Values p) (h1Data p),
    pcfTable_eq p hp (h1Values p) (h1Data p) rfl⟩

theorem h1_pcf_box_unbox : PcfBox.unbox (@h1_pcf_box n) = @h1_pcf_fast n := by
  funext p hp
  rfl

/-- The `h_1`-maximiser precondition-choice function, in a box, built from action data that is
supplied by the caller: a round of the recursion hands in the data it already has instead of
letting the `h^max` fixpoint extract it again. -/
def h1_pcf_boxD : PcfData (n + 2) :=
  fun p hp d hd => ⟨h1_pcf_of p hp (h1ValuesOf p d hd), pcfTable (h1ValuesOf p d hd) d,
    pcfTable_eq p hp (h1ValuesOf p d hd) d hd⟩

/-- Run with the real action data, the data-parameterised box is the boxed choice function. -/
theorem h1_pcf_boxD_unbox : PcfData.unbox (@h1_pcf_boxD n) = @h1_pcf_box n := rfl

/-- **The implementation of `lmcut_fast` that is actually run**: the same recursion, with the
precondition-choice function built once per round instead of once per query, and with the static
action data carried from round to round. -/
def lmcut_run (prob : PlanningTask n) (s : BitVec n) : ℕ∞ :=
  lmcut_box_sh prob s h1_pcf_boxD

@[csimp] theorem lmcut_fast_eq_run : @lmcut_fast = @lmcut_run := by
  funext n prob s
  rw [lmcut_run, lmcut_box_sh_eq, h1_pcf_boxD_unbox, lmcut_box_eq, h1_pcf_box_unbox, lmcut_fast]

end STRIPS
