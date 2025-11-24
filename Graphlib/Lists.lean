import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Data.Bool.AllAny
import Mathlib.Data.FinEnum

set_option trace.split.failure true

-- theorems for `List.Pairwise`. Needed for extension of Paths with new edges, due to need to modify Nodup proofs.
theorem pairwise_add_anywhere {α: Type} {pr: α → α → Prop} {l1 l2 : List α} {symm: Symmetric pr} {a : α}:
    (∀ (a' : α), a' ∈ l1 ∨ a' ∈ l2 → pr a a') ∧ (List.Pairwise pr (l1 ++ l2))
    → (List.Pairwise pr (l1 ++ (a :: l2)))   := by
    intro ⟨ allhold, rest_of_list ⟩
    induction l1
    case nil =>
      simp
      simp at rest_of_list
      constructor
      case left =>
        intro a' inl2
        apply allhold
        right
        exact inl2
      case right => exact rest_of_list
    case cons l ls IH =>
      simp
      constructor
      case left =>
        intro a' cond
        by_cases isa : a' = a
        case pos =>
          apply symm
          simp [isa]
          apply allhold
          left
          simp
        case neg =>
          simp at rest_of_list
          have ⟨ all_condition, rest_list⟩ := rest_of_list
          apply all_condition
          cases cond
          case a.inl apinls =>
            left
            exact apinls
          case a.inr some_or =>
          cases some_or
          case inl apisa =>
            contradiction
          case inr apinl2 =>
            right
            exact apinl2
      case right =>
        apply IH
        · intro a' stuff
          apply allhold
          cases stuff
          case inl ainls =>
            left
            simp
            right
            exact ainls
          case inr ainl2=>
            right
            exact ainl2
        · simp at rest_of_list
          have ⟨ all, rest⟩ := rest_of_list
          exact rest


theorem pairwise_additional_does_not_matter {α: Type} {pr: α → α → Prop} {l1 l2 : List α} {a : α}:
    (List.Pairwise pr (l1 ++ (a :: l2))) → (List.Pairwise pr (l1 ++ l2)) := by
    induction l1
    case nil =>
      simp
    case cons l l1s IH =>
      intro longList
      simp
      constructor
      case left =>
        intro b condition
        simp at longList
        cases condition
        case inl binl1s =>
          have foo := longList.left
          apply foo
          left
          exact binl1s
        case inr binl2 =>
          have foo := longList.left
          apply foo
          right
          right
          exact binl2
      case right =>
        apply IH
        simp at longList
        exact longList.right

theorem pairwise_elem_after {α: Type} {pr: α → α → Prop} {l1 l2 : List α} {x a : α}:
    (List.Pairwise pr (l1 ++ (a :: l2))) ∧ (x ∈ l2) → pr a x := by
    intro ⟨ full_list_pairwise, xinl2 ⟩
    induction l1
    case nil => simp_all
    case cons l lss IH =>
      simp at full_list_pairwise
      apply IH
      exact full_list_pairwise.right

theorem pairwise_elem_before {α: Type} {pr: α → α → Prop} {l1 l2 : List α} {x a : α}:
    (List.Pairwise pr (l1 ++ (a :: l2))) ∧ (x ∈ l1) → pr x a := by
    intro ⟨ full_list_pairwise, xinl1 ⟩
    induction l1
    case nil => simp_all
    case cons l lss IH =>
      simp at full_list_pairwise
      have ⟨ all, rest_of_list ⟩ := full_list_pairwise
      simp at xinl1
      cases xinl1
      case inl xisl =>
        rw [xisl]
        apply all
        right
        left
        rfl
      case inr xinRest =>
        apply IH
        · exact rest_of_list
        · exact xinRest


lemma listFind_general
  (α : Type)
  (list : List α)
  (p : α → Bool)
  (hasElem : (list.findFinIdx? p).isSome) :
    p list[(list.findFinIdx? p).get hasElem] := by
  rcases Option.isSome_iff_exists.1 hasElem with ⟨i, def_some_i⟩
  simp_rw [def_some_i] -- MG: normal "simp" did not work here, but this does!
  rw [List.findFinIdx?_eq_some_iff] at def_some_i
  simp_all



def maximum_of_non_empty_list {α : Type u_1} [Max α]
  (l : List α) (non_empty : l ≠ []) : α :=
    let maxOption := l.max?
    maxOption.get (by
      unfold maxOption
      rw [Option.isSome_iff_ne_none]
      simp_all)

theorem maximum_of_non_empty_le (l : List Nat) (non_empty : l ≠ []):
    ∀ x ∈ l, x ≤ maximum_of_non_empty_list l non_empty := by
    intro x x_in_l
    unfold maximum_of_non_empty_list
    simp_all
    apply List.le_max?_get_of_mem
    use x_in_l



