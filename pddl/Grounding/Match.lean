import pddl.Grounding.Compile

/-!
# Matching action schemas against a set of atoms

Naive full grounding enumerates *all* type-correct instantiations of every action schema,
which is exponential in the number of parameters.  The reachability grounder of
`pddl.Grounding.Reach` instead instantiates a schema by *matching* the positive atoms of
its precondition against a list `R` of atoms (the atoms that can possibly become true),
in the style of a Datalog join: each precondition atom is unified with the atoms of `R`
that have the same predicate, which binds parameters to objects, and only the parameters
that do not occur in a positive precondition atom are enumerated over their type.

This module defines that matching and proves it *complete*: every type-correct argument
list whose positive precondition atoms all belong to `R` is enumerated
(`reachInstantiations_complete`).  Completeness is what the correctness proof of the
reachability grounder needs — the enumeration may well produce spurious argument lists,
since the operators produced from them are checked against the real precondition anyway.
-/

namespace PDDL

/-! ### The positive atoms of a precondition -/

namespace Formula

/-- The atoms occurring positively in the top level conjunction of a formula.  These are
necessary conditions for the formula to hold, and are used to match a schema against a set
of atoms.  Atoms below negations, disjunctions or quantifiers are ignored, which is sound
for this purpose: using fewer necessary conditions only makes the enumeration larger. -/
def posConjAtoms : Formula → List (Name × List Term)
  | .atom p args => [(p, args)]
  | .conj f g => posConjAtoms f ++ posConjAtoms g
  | _ => []

theorem holds_posConjAtoms {I : Instance} {σ : Assign} {s : State} {f : Formula}
    (h : Holds I σ s f) : ∀ pa ∈ f.posConjAtoms, groundAtom σ pa.1 pa.2 ∈ s := by
  induction f with
  | atom p args =>
    intro pa hpa
    simp only [posConjAtoms, List.mem_singleton] at hpa
    subst hpa
    exact h
  | conj f g ihf ihg =>
    intro pa hpa
    simp only [posConjAtoms, List.mem_append] at hpa
    rcases hpa with hpa | hpa
    · exact ihf h.1 pa hpa
    · exact ihg h.2 pa hpa
  | _ => intro pa hpa; simp [posConjAtoms] at hpa

end Formula

/-! ### Partial substitutions -/

/-- A partial substitution: a list of variable/object pairs. -/
abbrev PSubst := List (Name × Name)

namespace PSubst

/-- The object bound to a variable, if any. -/
def get (s : PSubst) (v : Name) : Option Name := (s.find? (fun p => p.1 == v)).map (·.2)

/-- The partial substitution is consistent with the total assignment `σ`. -/
def Refines (s : PSubst) (σ : Assign) : Prop := ∀ p ∈ s, σ p.1 = p.2

theorem get_eq {s : PSubst} {v x : Name} (h : s.get v = some x) : (v, x) ∈ s := by
  simp only [get, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, rfl⟩ := h
  have hmem := List.mem_of_find?_eq_some hp
  have : p.1 = v := by simpa using List.find?_some hp
  rw [← this]
  simpa using hmem

theorem Refines.get {s : PSubst} {σ : Assign} (h : s.Refines σ) {v x : Name}
    (hx : s.get v = some x) : σ v = x := h _ (get_eq hx)

end PSubst

/-! ### Unification -/

/-- Unify a term with an object under a partial substitution. -/
def unifyTerm (s : PSubst) : Term → Name → Option PSubst
  | .obj o, x => if o == x then some s else none
  | .var v, x =>
      match s.get v with
      | some y => if y == x then some s else none
      | none => some ((v, x) :: s)

/-- Unify a list of terms with a list of objects. -/
def unifyArgs (s : PSubst) : List Term → List Name → Option PSubst
  | [], [] => some s
  | t :: ts, x :: xs => do
      let s' ← unifyTerm s t x
      unifyArgs s' ts xs
  | _, _ => none

theorem unifyTerm_complete {s : PSubst} {σ : Assign} (hs : s.Refines σ) (t : Term)
    (x : Name) (h : t.inst σ = x) : ∃ s', unifyTerm s t x = some s' ∧ s'.Refines σ := by
  cases t with
  | obj o =>
    simp only [Term.inst] at h
    subst h
    exact ⟨s, by simp [unifyTerm], hs⟩
  | var v =>
    simp only [Term.inst] at h
    cases hget : s.get v with
    | some y =>
      have : y = x := by rw [← hs.get hget, h]
      subst this
      exact ⟨s, by simp [unifyTerm, hget], hs⟩
    | none =>
      refine ⟨(v, x) :: s, by simp [unifyTerm, hget], ?_⟩
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact h
      · exact hs p hp

theorem unifyArgs_complete {σ : Assign} : ∀ (ts : List Term) (s : PSubst),
    s.Refines σ → ∃ s', unifyArgs s ts (ts.map (Term.inst σ)) = some s' ∧ s'.Refines σ := by
  intro ts
  induction ts with
  | nil => intro s hs; exact ⟨s, by simp [unifyArgs], hs⟩
  | cons t ts ih =>
    intro s hs
    obtain ⟨s₁, h₁, hs₁⟩ := unifyTerm_complete hs t (t.inst σ) rfl
    obtain ⟨s₂, h₂, hs₂⟩ := ih s₁ hs₁
    exact ⟨s₂, by simp [unifyArgs, h₁, h₂], hs₂⟩

/-! ### Joining the precondition atoms -/

/-- All extensions of `s` that unify the atom `pa` with an atom of `R`. -/
def matchAtom (R : List Atom) (pa : Name × List Term) (s : PSubst) : List PSubst :=
  R.filterMap (fun a => if a.pred == pa.1 then unifyArgs s pa.2 a.args else none)

/-- All extensions of `s` that unify every atom of `pas` with an atom of `R`. -/
def joinAtoms (R : List Atom) : List (Name × List Term) → PSubst → List PSubst
  | [], s => [s]
  | pa :: pas, s => (matchAtom R pa s).flatMap (joinAtoms R pas)

theorem matchAtom_complete {R : List Atom} {σ : Assign} {pa : Name × List Term}
    {s : PSubst} (hs : s.Refines σ) (h : groundAtom σ pa.1 pa.2 ∈ R) :
    ∃ s' ∈ matchAtom R pa s, s'.Refines σ := by
  obtain ⟨s', hunif, hs'⟩ := unifyArgs_complete pa.2 s hs
  refine ⟨s', ?_, hs'⟩
  simp only [matchAtom, List.mem_filterMap]
  refine ⟨groundAtom σ pa.1 pa.2, h, ?_⟩
  simp only [groundAtom, beq_self_eq_true, if_pos]
  exact hunif

theorem joinAtoms_complete {R : List Atom} {σ : Assign} :
    ∀ (pas : List (Name × List Term)) (s : PSubst), s.Refines σ →
      (∀ pa ∈ pas, groundAtom σ pa.1 pa.2 ∈ R) →
      ∃ s' ∈ joinAtoms R pas s, s'.Refines σ := by
  intro pas
  induction pas with
  | nil => intro s hs _; exact ⟨s, by simp [joinAtoms], hs⟩
  | cons pa pas ih =>
    intro s hs hmem
    obtain ⟨s₁, hs₁mem, hs₁⟩ := matchAtom_complete hs (hmem pa List.mem_cons_self)
    obtain ⟨s₂, hs₂mem, hs₂⟩ := ih s₁ hs₁ (fun p hp => hmem p (List.mem_cons_of_mem _ hp))
    exact ⟨s₂, List.mem_flatMap.2 ⟨s₁, hs₁mem, hs₂mem⟩, hs₂⟩

/-! ### Ordering the precondition atoms

The order in which the precondition atoms are joined is irrelevant for the *result* of the
matching but crucial for its cost: joining two atoms that share no variable forms their
cross product.  In benchmark domains that encode types as unary predicates (for example
`logistics`, whose `drive-truck` schema has the four type atoms `(truck ?t)`,
`(location ?from)`, `(location ?to)`, `(city ?c)` besides `(at ?t ?from)` and the two
`in-city` atoms) the textual order produces intermediate results of over a million partial
substitutions, while a connected order keeps them in the hundreds.

`orderAtoms` therefore reorders the atoms greedily: it always picks an atom with as many
already bound variables as possible and, among those, one with the fewest new variables.
Only one property of the reordering is needed for the correctness of the grounder, namely
that it produces atoms of the original list (`mem_orderAtoms`); this is what makes the
completeness proof of the matching go through unchanged. -/

/-- The variables occurring in a precondition atom. -/
def atomVars (pa : Name × List Term) : List Name :=
  pa.2.filterMap (fun t => match t with | .var v => some v | _ => none)

/-- The number of variables of `pa` that are already bound, and the number of those that
are not. -/
def atomScore (bound : List Name) (pa : Name × List Term) : Nat × Nat :=
  let vars := atomVars pa
  ((vars.filter (fun v => bound.contains v)).length,
    ((vars.filter (fun v => !bound.contains v)).eraseDups).length)

/-- `s` is a better score than `s'`: more bound variables, or as many bound variables and
fewer new ones. -/
def betterScore (s s' : Nat × Nat) : Bool := s.1 > s'.1 || (s.1 == s'.1 && s.2 < s'.2)

/-- The index of the atom to join next. -/
def bestAtomIdx (bound : List Name) (pas : List (Name × List Term)) : Nat :=
  match pas.zipIdx with
  | [] => 0
  | (pa, i) :: rest =>
      (rest.foldl
        (fun (best : (Nat × Nat) × Nat) (q : (Name × List Term) × Nat) =>
          let s := atomScore bound q.1
          if betterScore s best.1 then (s, q.2) else best)
        (atomScore bound pa, i)).2

/-- The precondition atoms, reordered so that atoms sharing variables with the already
processed ones come first. -/
def orderAtoms (bound : List Name) (pas : List (Name × List Term)) :
    List (Name × List Term) :=
  match hp : pas[bestAtomIdx bound pas]? with
  | none => pas
  | some pa =>
      have h : bestAtomIdx bound pas < pas.length := (List.getElem?_eq_some_iff.1 hp).1
      have : (pas.eraseIdx (bestAtomIdx bound pas)).length < pas.length := by
        rw [List.length_eraseIdx, if_pos h]
        omega
      pa :: orderAtoms (bound ++ atomVars pa) (pas.eraseIdx (bestAtomIdx bound pas))
  termination_by pas.length

/-- The reordering only produces atoms of the original list. -/
theorem mem_orderAtoms : ∀ (bound : List Name) (pas : List (Name × List Term))
    (pa : Name × List Term), pa ∈ orderAtoms bound pas → pa ∈ pas := by
  intro bound pas
  induction hn : pas.length using Nat.strong_induction_on generalizing bound pas with
  | _ n ih =>
    subst hn
    intro pa hmem
    rw [orderAtoms] at hmem
    split at hmem
    · exact hmem
    · rename_i q hq
      have h : bestAtomIdx bound pas < pas.length := (List.getElem?_eq_some_iff.1 hq).1
      rcases List.mem_cons.1 hmem with rfl | hmem
      · exact List.mem_of_getElem? hq
      · have hlt : (pas.eraseIdx (bestAtomIdx bound pas)).length < pas.length := by
          rw [List.length_eraseIdx, if_pos h]
          omega
        have := ih _ hlt _ _ rfl pa hmem
        exact (List.eraseIdx_sublist pas (bestAtomIdx bound pas)).mem this

/-! ### Completing a partial substitution to an argument list -/

/-- All argument lists compatible with the partial substitution `s`: a parameter bound by
`s` takes its value, an unbound parameter ranges over the objects of its type. -/
def completeArgs (I : Instance) (s : PSubst) : List TypedVar → List (List Name)
  | [] => [[]]
  | p :: ps =>
      match s.get p.name with
      | some o => (completeArgs I s ps).map (fun args => o :: args)
      | none =>
          (I.objectsOfTypeL p.type).flatMap
            (fun o => (completeArgs I s ps).map (fun args => o :: args))

theorem completeArgs_complete {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    {s : PSubst} {σ : Assign} (hs : s.Refines σ) :
    ∀ (params : List TypedVar) (args : List Name),
      I.ArgsWellTyped params args →
      List.Forall₂ (fun (p : TypedVar) (o : Name) => σ p.name = o) params args →
      args ∈ completeArgs I s params := by
  intro params
  induction params with
  | nil =>
    intro args _ hσ
    cases hσ
    simp [completeArgs]
  | cons p ps ih =>
    intro args hty hσ
    cases hσ with
    | cons hp hps =>
      rename_i o args'
      cases hty with
      | cons htyp htys =>
        have hrest : args' ∈ completeArgs I s ps := ih args' htys hps
        cases hget : s.get p.name with
        | some y =>
          have : y = o := by rw [← hs.get hget, hp]
          subst this
          simp only [completeArgs, hget, List.mem_map]
          exact ⟨args', hrest, rfl⟩
        | none =>
          simp only [completeArgs, hget, List.mem_flatMap, List.mem_map]
          exact ⟨o, (Instance.mem_objectsOfTypeL_iff hwf o p.type).2 htyp, args', hrest, rfl⟩

/-! ### Instantiating a schema against a list of atoms -/

/-- Weakening a `Forall₂` statement, using membership in the left list. -/
theorem forall₂_mono_mem {α β : Type} {R S : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
      (∀ a ∈ l₁, ∀ b, R a b → S a b) → List.Forall₂ S l₁ l₂ := by
  intro l₁ l₂ h
  induction h with
  | nil => intro _; exact List.Forall₂.nil
  | @cons a b as bs hab _ ih =>
    intro hRS
    exact List.Forall₂.cons (hRS a List.mem_cons_self b hab)
      (ih (fun x hx y hxy => hRS x (List.mem_cons_of_mem _ hx) y hxy))

theorem bind_cons_head (p : TypedVar) (ps : List TypedVar) (o : Name) (os : List Name) :
    bind (p :: ps) (o :: os) p.name = o := by
  simp [bind]

theorem bind_cons_ne {p : TypedVar} {ps : List TypedVar} {o : Name} {os : List Name}
    {v : Name} (h : v ≠ p.name) : bind (p :: ps) (o :: os) v = bind ps os v := by
  simp [bind, Ne.symm h]

/-- The assignment `bind params args` maps the name of each parameter to the corresponding
argument, provided the parameter names are pairwise distinct. -/
theorem bind_forall₂ : ∀ (params : List TypedVar) (args : List Name),
    (params.map (·.name)).Nodup → params.length = args.length →
    List.Forall₂ (fun (p : TypedVar) (o : Name) => bind params args p.name = o)
      params args := by
  intro params
  induction params with
  | nil =>
    intro args _ hlen
    cases args with
    | nil => exact List.Forall₂.nil
    | cons a as => simp at hlen
  | cons p ps ih =>
    intro args hnd hlen
    cases args with
    | nil => simp at hlen
    | cons o os =>
      simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
      refine List.Forall₂.cons (bind_cons_head p ps o os) ?_
      refine forall₂_mono_mem (ih os hnd.2 (by simpa using hlen)) ?_
      intro q hq x hqx
      have hne : q.name ≠ p.name := fun hqp => hnd.1 q hq hqp
      rw [bind_cons_ne hne]
      exact hqx

/-- All instantiations of a schema obtained by matching the positive atoms of its
precondition against `R`.  Schemas with repeated parameter names (which real PDDL does not
have) fall back to full enumeration. -/
def reachInstantiations (I : Instance) (R : List Atom) (a : Action) : List (List Name) :=
  if (a.params.map (·.name)).Nodup then
    ((joinAtoms R (orderAtoms [] a.pre.posConjAtoms) []).flatMap
      (fun s => completeArgs I s a.params)).filter (I.argsWellTypedB a.params)
  else
    I.instantiations a.params

theorem reachInstantiations_wellTyped {I : Instance}
    (hwf : I.domain.typesWellFormedB = true) {R : List Atom} {a : Action} {args : List Name}
    (h : args ∈ reachInstantiations I R a) : I.ArgsWellTyped a.params args := by
  simp only [reachInstantiations] at h
  split at h
  · have := List.of_mem_filter h
    exact (Instance.argsWellTypedB_iff hwf _ _).1 this
  · exact (Instance.mem_instantiations_iff hwf _ _).1 h

/-- **Completeness of the matching**: every type-correct argument list all of whose
positive precondition atoms belong to `R` is enumerated. -/
theorem reachInstantiations_complete {I : Instance}
    (hwf : I.domain.typesWellFormedB = true) {R : List Atom} {a : Action} {args : List Name}
    (hty : I.ArgsWellTyped a.params args)
    (hpre : ∀ pa ∈ a.pre.posConjAtoms,
      groundAtom (bind a.params args) pa.1 pa.2 ∈ R) :
    args ∈ reachInstantiations I R a := by
  simp only [reachInstantiations]
  split
  · rename_i hnd
    obtain ⟨s, hsmem, hs⟩ :=
      joinAtoms_complete (σ := bind a.params args) (orderAtoms [] a.pre.posConjAtoms) []
        (by simp [PSubst.Refines])
        (fun pa hpa => hpre pa (mem_orderAtoms [] _ pa hpa))
    refine List.mem_filter.2 ⟨?_, (Instance.argsWellTypedB_iff hwf _ _).2 hty⟩
    refine List.mem_flatMap.2 ⟨s, hsmem, ?_⟩
    exact completeArgs_complete hwf hs a.params args hty
      (bind_forall₂ a.params args hnd hty.length_eq)
  · exact (Instance.mem_instantiations_iff hwf _ _).2 hty

end PDDL
