import Mathlib.Data.Bool.AllAny
import Mathlib.Data.FinEnum
import Mathlib.Data.Finset.Empty
import Mathlib.Data.List.MinMax

import Graphlib.Lists
import Graphlib.FinEnum
import Graphlib.Basic
import Graphlib.DFS2

set_option trace.split.failure true
--set_option diagnostics true

-- def local global variable for a graph
variable {V : Type} {E : Type} [FinEnum V] [DecidableEq V] [DecidableEq E]
variable (G : WeightedDiGraph V E)



def maximum_path_order_of [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E)
    (dfs_state : dfs_state g)
    (states : Finset V)
    (non_empty : states ≠ ∅): Nat :=
  let vList : List V := (FinEnum.toList states)
  have vListNonEmpty : vList ≠ [] := by
    unfold vList
    intro a
    simp_all
    have statesEmpty : states = ∅ := by
      by_cases h : ∃ x, x ∈ states
      · obtain ⟨s, s_in_states⟩ := h
        have hh : s ∈ (FinEnum.toList { x // x ∈ states }).unattach := by
          clear a
          simp_all only [List.mem_unattach, FinEnum.mem_toList, exists_const]
        simp_all 
      · ext y
        simp_all only [not_exists, Finset.notMem_empty]
    contradiction
  let opt : Option Nat := List.max? (vList.map (λ s => dfs_state.pathOrder s))

  have optNotBot : opt ≠ none := by 
    unfold opt
    intro _
    simp_all
  Option.get opt (by
    unfold Option.isSome
    unfold opt
    split
    · rfl
    · simp_all
  )

lemma maximum_path_order_is_le 
    (g: WeightedDiGraph V E)
    (dfs_state : dfs_state g)
    (states : Finset V)
    (non_empty : states ≠ ∅):
    ∀ s ∈ states, dfs_state.pathOrder s ≤ maximum_path_order_of g dfs_state states non_empty := by
    intro s s_in_states
    unfold maximum_path_order_of
    simp_all
    apply maximum_of_non_empty_le
    · simp_all
      apply List.ne_nil_of_mem
      rotate_right
      · use s
      · simp_all
    · simp_all
      use s
