import Mathlib.Data.FinEnum

variable {V : Type} [FinEnum V] [DecidableEq V]

-- currently unused. Proof needed to be inlined in maximum_path_order_of
theorem FinEnum.empty_to_list_empty_set (states : Finset V):
      (FinEnum.toList { x // x ∈ states }).unattach = [] → states = ∅ := by
  intro toListEmpty
  by_cases h : ∃ x, x ∈ states
  · obtain ⟨s, s_in_states⟩ := h
    have hh : s ∈ (FinEnum.toList { x // x ∈ states }).unattach := by
      clear toListEmpty
      simp_all only [List.mem_unattach, mem_toList, exists_const]
    simp_all 
  · simp_all only [not_exists]
    ext a : 1
    simp_all only [Finset.notMem_empty]


