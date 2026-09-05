import Mathlib.Data.FinEnum
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# A cheap enumeration for `FinEnum (Fin n)`

Every list of "all vertices" in the LM-cut machinery is obtained from the `FinEnum` instance of
the vertex type, and the vertex type is always `Fin n`.  Mathlib's instance
`FinEnum.fin n = FinEnum.ofList (List.finRange n) _` builds its enumeration by *deduplicating*
`List.finRange n` and indexing into the deduplicated list, so enumerating the `n` vertices costs
`Θ(n²)` comparisons — and the enumeration is rebuilt on every call.

`finEnumFinFast` is the same instance with the identity equivalence.  The two are equal
(`finEnum_fin_eq_fast`, proved through the extensionality lemma `finEnum_ext`), so the equality is
installed with `@[csimp]`: nothing that is stated about `FinEnum (Fin n)` changes, but the
compiled code enumerates `Fin n` in linear time.
-/

/-- Two `FinEnum` structures on the same type are equal as soon as they have the same cardinality
and the same numbering. -/
theorem finEnum_ext {α : Type} (a b : FinEnum α) (h : a.card = b.card)
    (he : ∀ x, ((a.equiv x : Fin a.card) : ℕ) = ((b.equiv x : Fin b.card) : ℕ)) : a = b := by
  obtain ⟨ca, ea, da⟩ := a
  obtain ⟨cb, eb, db⟩ := b
  simp only at h he
  subst h
  have hee : ea = eb := Equiv.ext fun x => Fin.ext (he x)
  subst hee
  congr 1
  exact Subsingleton.elim _ _

/-- The `FinEnum (Fin n)` instance that numbers `Fin n` by the identity. -/
@[implicit_reducible] def finEnumFinFast (n : ℕ) : FinEnum (Fin n) where
  card := n
  equiv := Equiv.refl _
  decEq := inferInstance

/-- **`Fin n` is enumerated by the identity.** -/
@[csimp] theorem finEnum_fin_eq_fast : @FinEnum.fin = @finEnumFinFast := by
  funext n
  have hcard : (FinEnum.fin (n := n)).card = n := by
    show (List.finRange n).dedup.length = n
    rw [List.dedup_eq_self.mpr (List.nodup_finRange n), List.length_finRange]
  refine finEnum_ext _ _ hcard ?_
  intro x
  show ((List.idxOf x (List.finRange n).dedup : ℕ)) = (x : ℕ)
  rw [List.dedup_eq_self.mpr (List.nodup_finRange n)]
  simp [List.idxOf_finRange]

/-! ## Enumerating a type through `Finset.univ`

`FinEnum.toList (Finset.univ : Finset V)` enumerates the *subtype* `↥(Finset.univ : Finset V)`,
which filters and deduplicates the enumeration of `V` and then indexes into the result: `Θ(|V|²)`
work, and a decidable-membership test in a `Finset` for each element.  It produces exactly
`FinEnum.toList V` (`toList_univ_subtype`). -/

private theorem toList_ofNodupList {α : Type} [DecidableEq α] (xs : List α) (h : ∀ x, x ∈ xs)
    (h' : xs.Nodup) : @FinEnum.toList α (FinEnum.ofNodupList xs h h') = xs :=
  List.map_get_finRange xs

private theorem toList_ofList {α : Type} [DecidableEq α] (xs : List α) (h : ∀ x, x ∈ xs)
    (h' : xs.Nodup) : @FinEnum.toList α (FinEnum.ofList xs h) = xs := by
  rw [FinEnum.ofList, toList_ofNodupList, List.dedup_eq_self.mpr h']

/-- Enumerating the subtype of `Finset.univ` is enumerating the type. -/
theorem toList_univ_subtype (V : Type) [FinEnum V] :
    ((FinEnum.toList {x : V // x ∈ (Finset.univ : Finset V)}).map Subtype.val)
      = FinEnum.toList V := by
  have hxs : (List.filterMap (fun x => if h : x ∈ (Finset.univ : Finset V) then
        some (⟨x, h⟩ : {x : V // x ∈ (Finset.univ : Finset V)}) else none) (FinEnum.toList V))
      = (FinEnum.toList V).map (fun x => ⟨x, Finset.mem_univ x⟩) := by
    induction FinEnum.toList V with
    | nil => simp
    | cons a l ih => simp [ih]
  have hnd : ((FinEnum.toList V).map
      (fun x => (⟨x, Finset.mem_univ x⟩ : {x : V // x ∈ (Finset.univ : Finset V)}))).Nodup := by
    refine List.Nodup.map ?_ FinEnum.nodup_toList
    intro a b h
    simpa using h
  have hlist := toList_ofList (α := {x : V // x ∈ (Finset.univ : Finset V)})
    (List.filterMap (fun x => if h : x ∈ (Finset.univ : Finset V) then
        some (⟨x, h⟩ : {x : V // x ∈ (Finset.univ : Finset V)}) else none) (FinEnum.toList V))
    (by rw [hxs]; intro x; exact List.mem_map.mpr ⟨x.1, FinEnum.mem_toList _, by cases x; rfl⟩)
    (by rw [hxs]; exact hnd)
  rw [show (FinEnum.toList {x : V // x ∈ (Finset.univ : Finset V)}) = _ from hlist, hxs,
    List.map_map]
  exact (List.map_congr_left (fun _ _ => rfl)).trans (List.map_id _)
