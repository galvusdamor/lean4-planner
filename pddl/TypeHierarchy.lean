import pddl.Semantics
import Mathlib.Data.Finset.Lattice.Basic

/-!
# Deciding the subtype relation

The semantics in `pddl.Semantics` defines the subtype relation `Domain.TypeLE` as the
reflexive-transitive closure of the declared type edges, which is a `Prop` and hence not
directly executable.  This module provides an executable upward closure computation
`ancestors?` on the type graph, and shows that it decides `Domain.TypeLE`:

* `typeLEB_sound`: whenever the check succeeds, the subtype relation really holds;
* `typeLEB_complete`: whenever the closure computation reached a fixpoint (which
  `Domain.typesWellFormed` checks, and which holds for every acyclic type hierarchy), the
  check succeeds for all pairs in the subtype relation.

The computation deliberately verifies at runtime that a fixpoint was reached, so that no
assumption about the shape of the type hierarchy (in particular no acyclicity assumption)
has to be built into the statements.
-/

namespace PDDL

/-- One step of the upward closure of a set of type names along the type edges `es`. -/
def ancStep (es : List (Name × Name)) (S : Finset Name) : Finset Name :=
  S ∪ (es.filterMap (fun p => if p.1 ∈ S then some p.2 else none)).toFinset

theorem mem_ancStep {es : List (Name × Name)} {S : Finset Name} {x : Name} :
    x ∈ ancStep es S ↔ x ∈ S ∨ ∃ y ∈ S, (y, x) ∈ es := by
  simp only [ancStep, Finset.mem_union, List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro (h | ⟨⟨y, z⟩, hmem, hf⟩)
    · exact Or.inl h
    · by_cases hy : y ∈ S
      · simp only [hy, if_true, Option.some.injEq] at hf
        exact Or.inr ⟨y, hy, hf ▸ hmem⟩
      · simp [hy] at hf
  · rintro (h | ⟨y, hy, hmem⟩)
    · exact Or.inl h
    · exact Or.inr ⟨(y, x), hmem, by simp [hy]⟩

theorem subset_ancStep (es : List (Name × Name)) (S : Finset Name) : S ⊆ ancStep es S :=
  fun _ hx => mem_ancStep.2 (Or.inl hx)

/-- Iterate `ancStep` `n` times. -/
def ancIter (es : List (Name × Name)) : Nat → Finset Name → Finset Name
  | 0, S => S
  | n + 1, S => ancIter es n (ancStep es S)

theorem subset_ancIter (es : List (Name × Name)) (n : Nat) (S : Finset Name) :
    S ⊆ ancIter es n S := by
  induction n generalizing S with
  | zero => exact fun _ h => h
  | succ n ih => exact fun _ h => ih _ (subset_ancStep es S h)

theorem ancIter_eq_of_fixed {es : List (Name × Name)} {S : Finset Name}
    (h : ancStep es S = S) (n : Nat) : ancIter es n S = S := by
  induction n generalizing S with
  | zero => rfl
  | succ n ih => rw [ancIter, h, ih h]

/-- Reachability in the type graph, i.e. the underlying relation of `Domain.TypeLE`. -/
abbrev EdgeStep (es : List (Name × Name)) (a b : Name) : Prop := (a, b) ∈ es

theorem reachable_of_mem_ancIter {es : List (Name × Name)} {n : Nat} {S : Finset Name}
    {x : Name} (hx : x ∈ ancIter es n S) :
    ∃ y ∈ S, Relation.ReflTransGen (EdgeStep es) y x := by
  induction n generalizing S with
  | zero => exact ⟨x, hx, Relation.ReflTransGen.refl⟩
  | succ n ih =>
    obtain ⟨y, hy, hpath⟩ := ih hx
    rcases mem_ancStep.1 hy with h | ⟨z, hz, hedge⟩
    · exact ⟨y, h, hpath⟩
    · exact ⟨z, hz, (Relation.ReflTransGen.single hedge).trans hpath⟩

theorem mem_of_reachable_of_closed {es : List (Name × Name)} {S : Finset Name}
    (hclosed : ancStep es S ⊆ S) {y x : Name} (hy : y ∈ S)
    (h : Relation.ReflTransGen (EdgeStep es) y x) : x ∈ S := by
  induction h with
  | refl => exact hy
  | tail _ hedge ih => exact hclosed (mem_ancStep.2 (Or.inr ⟨_, ih, hedge⟩))

/-- The upward closure of `{t}` in the type graph of `d`, computed with a fixed number of
iterations. -/
def ancestorsRaw (d : Domain) (t : Name) : Finset Name :=
  ancIter d.types (d.types.length + 1) {t}

/-- The upward closure of `{t}`, together with a runtime check that a fixpoint has been
reached.  Returns `none` if the iteration did not converge (which cannot happen for an
acyclic type hierarchy). -/
def ancestors? (d : Domain) (t : Name) : Option (Finset Name) :=
  if ancStep d.types (ancestorsRaw d t) ⊆ ancestorsRaw d t then some (ancestorsRaw d t)
  else none

/-- Executable subtype test. -/
def typeLEB (d : Domain) (t u : Name) : Bool :=
  match ancestors? d t with
  | some S => u ∈ S
  | none => t == u

theorem mem_ancestorsRaw_self (d : Domain) (t : Name) : t ∈ ancestorsRaw d t :=
  subset_ancIter _ _ _ (Finset.mem_singleton_self t)

/-- Soundness: if the executable test succeeds, the two types really are in the subtype
relation. -/
theorem eq_ancestorsRaw_of_ancestors? {d : Domain} {t : Name} {S : Finset Name}
    (h : ancestors? d t = some S) : S = ancestorsRaw d t := by
  unfold ancestors? at h
  split at h
  · exact (Option.some.inj h).symm
  · exact absurd h (by simp)

theorem typeLEB_sound {d : Domain} {t u : Name} (h : typeLEB d t u = true) : d.TypeLE t u := by
  unfold typeLEB at h
  cases hA : ancestors? d t with
  | none =>
    rw [hA] at h
    simp only [beq_iff_eq] at h
    exact h ▸ Relation.ReflTransGen.refl
  | some S =>
    rw [hA] at h
    simp only [decide_eq_true_eq] at h
    rw [eq_ancestorsRaw_of_ancestors? hA] at h
    obtain ⟨y, hy, hpath⟩ :=
      reachable_of_mem_ancIter (es := d.types) (n := d.types.length + 1) h
    rw [Finset.mem_singleton] at hy
    subst hy
    exact hpath

/-- Completeness: if the closure computation for `t` converged, then the executable test
succeeds for every supertype of `t`. -/
theorem typeLEB_complete {d : Domain} {t u : Name} (hconv : (ancestors? d t).isSome)
    (h : d.TypeLE t u) : typeLEB d t u = true := by
  unfold typeLEB
  unfold ancestors? at hconv ⊢
  split at hconv
  · rename_i hclosed
    rw [if_pos hclosed]
    simp only [decide_eq_true_eq]
    exact mem_of_reachable_of_closed hclosed (mem_ancestorsRaw_self d t) h
  · simp at hconv

/-- If a type name does not occur in the type hierarchy at all, its closure is trivially
converged. -/
theorem ancestors?_isSome_of_not_mem {d : Domain} {t : Name}
    (h : ∀ u, (t, u) ∉ d.types) : (ancestors? d t).isSome := by
  have hstep : ancStep d.types {t} = {t} := by
    apply Finset.Subset.antisymm _ (subset_ancStep _ _)
    intro x hx
    rcases mem_ancStep.1 hx with h' | ⟨y, hy, hedge⟩
    · exact h'
    · rw [Finset.mem_singleton] at hy
      subst hy
      exact absurd hedge (h x)
  have : ancestorsRaw d t = {t} := ancIter_eq_of_fixed hstep _
  unfold ancestors?
  simp [this, hstep]

/-- The check that the closure computation converges for all declared type names.  This is
the case for every acyclic type hierarchy, in particular for every hierarchy accepted by
the usual PDDL tools. -/
def Domain.typesWellFormedB (d : Domain) : Bool :=
  (typeNames d.types).all (fun t => (ancestors? d t).isSome)

theorem ancestors?_isSome_of_typesWellFormed {d : Domain} (h : d.typesWellFormedB = true)
    (t : Name) : (ancestors? d t).isSome := by
  by_cases ht : ∃ u, (t, u) ∈ d.types
  · obtain ⟨u, hu⟩ := ht
    have : t ∈ typeNames d.types := by
      simp only [typeNames, List.mem_eraseDups, List.mem_flatMap]
      exact ⟨(t, u), hu, by simp⟩
    simpa using (List.all_eq_true.1 h) t this
  · exact ancestors?_isSome_of_not_mem (by simpa using not_exists.1 ht)

/-- Under the well-formedness check, the executable subtype test decides the subtype
relation. -/
theorem typeLEB_iff {d : Domain} (hwf : d.typesWellFormedB = true) (t u : Name) :
    typeLEB d t u = true ↔ d.TypeLE t u :=
  ⟨typeLEB_sound, typeLEB_complete (ancestors?_isSome_of_typesWellFormed hwf t)⟩

/-! ### Deciding the typing of objects -/

namespace Instance

/-- Executable version of `Instance.HasType`. -/
def hasTypeB (I : Instance) (o : Name) (te : TypeExpr) : Bool :=
  match I.typeOf o with
  | none => false
  | some dte => dte.alts.any (fun dt => te.alts.any (fun t => typeLEB I.domain dt t))

theorem hasTypeB_sound {I : Instance} {o : Name} {te : TypeExpr} (h : I.hasTypeB o te = true) :
    I.HasType o te := by
  unfold hasTypeB at h
  cases hty : I.typeOf o with
  | none => rw [hty] at h; exact absurd h (by simp)
  | some dte =>
    rw [hty] at h
    simp only [List.any_eq_true] at h
    obtain ⟨dt, hdt, t, ht, hle⟩ := h
    exact ⟨dte, hty, dt, hdt, t, ht, typeLEB_sound hle⟩

theorem hasTypeB_complete {I : Instance} (hwf : I.domain.typesWellFormedB = true) {o : Name}
    {te : TypeExpr} (h : I.HasType o te) : I.hasTypeB o te = true := by
  obtain ⟨dte, hty, dt, hdt, t, ht, hle⟩ := h
  unfold hasTypeB
  rw [hty]
  simp only [List.any_eq_true]
  exact ⟨dt, hdt, t, ht, (typeLEB_iff hwf dt t).2 hle⟩

theorem hasTypeB_iff {I : Instance} (hwf : I.domain.typesWellFormedB = true) (o : Name)
    (te : TypeExpr) : I.hasTypeB o te = true ↔ I.HasType o te :=
  ⟨hasTypeB_sound, hasTypeB_complete hwf⟩

/-- Executable list of the objects of a given type. -/
def objectsOfTypeL (I : Instance) (te : TypeExpr) : List Name :=
  I.objects.filter (fun o => I.hasTypeB o te)

theorem mem_objectsOfTypeL_iff {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    (o : Name) (te : TypeExpr) : o ∈ I.objectsOfTypeL te ↔ I.HasType o te := by
  simp only [objectsOfTypeL, List.mem_filter]
  constructor
  · exact fun h => hasTypeB_sound h.2
  · exact fun h => ⟨h.mem_objects, hasTypeB_complete hwf h⟩

end Instance

end PDDL
