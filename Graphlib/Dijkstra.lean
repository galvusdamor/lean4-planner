import Mathlib.Data.Bool.AllAny
import Mathlib.Data.FinEnum
import Mathlib.Data.Finset.Empty
import Mathlib.Data.List.MinMax

import Graphlib.Lists
import Graphlib.FinEnum
import Graphlib.Basic
import Graphlib.NatGraph
import Graphlib.SearchState
import Graphlib.SearchAlgorithm
import Graphlib.SearchStep
import Mathlib.Order.Basic
import Init.SimpLemmas
import Init.Core

set_option trace.split.failure true
--set_option diagnostics true

-- def local global variable for a graph
variable {V : Type} [FinEnum V] [DecidableEq V]
variable {g : NatGraph V}


namespace Nat

instance : FValueComp (ℕ × ℕ) where
  lt (x y : ℕ × ℕ) : Bool := Prod.Lex (· < ·) (· < ·) x y
  wf := by
    simp
    apply Prod.Lex.instWellFoundedLTLex.wf
  lt_irr := by grind
  lt_trans := by grind
  lt_antisymm := by grind

end Nat



namespace NatGraph




-----------------------------------------------------------------------
------ Dijkstra implementation and proof ------


--abbrev dijkstra_search_state (g : NatGraph V) := WeightedDiGraph.base_search_state g (ℕ × Fin g.nodeNum)
abbrev dijkstra_search_state (g : NatGraph V) := WeightedDiGraph.base_search_state g (ℕ × ℕ)


    
@[simp]
def path_val (priorState : dijkstra_search_state g) (cur v : V) (adj : g.Adj cur v) : (ℕ × ℕ) := 
  ⟨ (priorState.pathOrder cur).fst + g.edgeCost adj, (priorState.pathOrder cur).snd + 1⟩

@[simp]
def new_cost (priorState : dijkstra_search_state g) (cur v : V) (adj : g.Adj cur v) :=
  if (priorState.pathOrder v).1 < (path_val priorState cur v adj).1 then 
    (priorState.pathOrder v)
  else if (priorState.pathOrder v).1 = (path_val priorState cur v adj).1 ∧ (priorState.pathOrder v).2 < (path_val priorState cur v adj).2 then 
    (priorState.pathOrder v)
  else
    (path_val priorState cur v adj)


def dijkstra_step_expand --[FinEnum V] [DecidableEq V]
    --(g: NatGraph V)
    (priorState : dijkstra_search_state g)
    (stackHead : V)
    (stackTail : List V):
    (dijkstra_search_state g) :=
      -- all neighbours that either are *not visited yet* or are not on stack (to avoid dupliactes) and have shorter path via stackHead
      let newly_visited : Finset V := (Finset.univ).filterMap
        (λ v => if h : @decide (g.Adj stackHead v) (g.instDecAdj stackHead v) then
            let adj : g.Adj stackHead v := by simp_all only [decide_eq_true_eq] 
            if v ∉ priorState.visited ∨
              (v ∈ priorState.visited ∧ v ∉ stackTail ∧ (priorState.pathOrder v).fst > (priorState.pathOrder stackHead).fst + g.edgeCost adj) then some v else none else none)
        (by intro a a' b a_1 a_2; simp_all) -- filter neighbors to expand the visited list
      
      let vList : List V := (FinEnum.toList (Finset.univ : Finset V))
      let newly_visited_list : List V := vList.filterMap (λ v => if v ∈ newly_visited then some v else none)
      let new_visited : Finset V := priorState.visited ∪ newly_visited


      let new_order : V → ℕ × ℕ := fun v  =>
        if h : @decide (g.Adj stackHead v) (g.instDecAdj stackHead v) then
          let adj : g.Adj stackHead v := by simp_all only [decide_eq_true_eq] 
          if (v ∉ priorState.visited) then path_val priorState stackHead v adj
          else new_cost priorState stackHead v adj
        else priorState.pathOrder v


      let new_mother : new_visited → V := fun ⟨v, hv⟩  =>
        if not_visited_before : (v ∉ priorState.visited) then
          stackHead
        else
          if priorState.pathOrder v = new_order v then
            priorState.mother ⟨v, by simp_all⟩
          else
            stackHead
        --if h : @decide (g.Adj stackHead v) (g.instDecAdj stackHead v) then
        --  let adj : g.Adj stackHead v := by simp_all only [decide_eq_true_eq] 
        --  if hh : (v ∉ priorState.visited) then stackHead 
        --  else
        --    if (priorState.pathOrder v).fst > ((priorState.pathOrder stackHead).fst + g.edgeCost adj) then
        --      stackHead
        --    else
        --      priorState.mother ⟨v, by simp_all⟩
        --else priorState.mother ⟨v, by grind⟩


     let new_stack : List V := (stackTail ++ newly_visited_list).mergeSort (fun a b =>
        new_order a ≤ new_order b) 
       
     WeightedDiGraph.base_search_state.mk new_visited new_order new_mother new_stack


def dijkstra_termination_metric 
    (s : dijkstra_search_state g): ℕ × ℕ :=
    (Fintype.card V - s.visited.card, s.stack.length)

--set_option trace.Meta.synthInstance true

lemma dijkstra_expand_metric_reduction : WeightedDiGraph.termination_proof_for_expand (G:=g) (state_type := dijkstra_search_state g) (D:=ℕ ×ℕ) (dijkstra_step_expand) goal dijkstra_termination_metric := by
    sorry







--lemma dijkstra_expand_newly_added_are_adjacent 
--    (priorState : dijkstra_search_state g)
--    (stackHead : V)
--    (stackTail : List V):
--    ∀ x : V, x ∉ priorState.visited ∧ x ∉ stackTail ∧
--      x ∈ (dijkstra_step_expand priorState stackHead stackTail).stack →  
--      g.Adj stackHead x := by
--    intro x ⟨x_not_visi, ⟨ x_not_on_stack_before, x_on_stack_after ⟩  ⟩
--    unfold dijkstra_step_expand at x_on_stack_after
--    simp_all
--
--
--lemma dijkstra_expand_keeps_stack_in_visited 
--    (priorState : dijkstra_search_state  g)
--    (stackHead : V)
--    (stackTail : List V):
--    WeightedDiGraph.search_invar_stack_is_visited priorState ∧
--      stackHead ∈ priorState.visited ∧ (∀ x : V, x ∉ priorState.visited → x ∉ stackTail) →
--      WeightedDiGraph.search_invar_stack_is_visited (dijkstra_step_expand priorState stackHead stackTail) := by
--      intro ⟨ stack_is_visited_prior, stackhead_visited, x_not_in_stack_tail⟩ 
--      unfold WeightedDiGraph.search_invar_stack_is_visited
--      intro x x_now_on_stack
--      unfold dijkstra_step_expand
--      simp_all
--      by_cases x_was_visited : x ∈ priorState.visited
--      · left
--        exact x_was_visited
--      · right
--        have adj : g.Adj stackHead x := by 
--          apply (dijkstra_expand_newly_added_are_adjacent priorState stackHead stackTail)
--          simp_all
--        use adj ; left ; exact x_was_visited
--
--
--lemma dijkstra_expand_keeps_mother_in_visited 
--    (priorState : dijkstra_search_state  g)
--    (stackHead : V)
--    (stackTail : List V):
--    WeightedDiGraph.search_invar_mother_is_visited priorState ∧ stackHead ∈ priorState.visited → WeightedDiGraph.search_invar_mother_is_visited (dijkstra_step_expand priorState stackHead stackTail) := by
--      intro mother_is_visited_prior
--      unfold WeightedDiGraph.search_invar_mother_is_visited
--      intro x
--      simp_all
--      unfold dijkstra_step_expand
--      simp_all
--      split
--      next adj_decide_true =>
--        split <;> left <;> try split <;> simp_all
--      · left
--        simp_all
--
--lemma dijkstra_expand_keeps_mother_is_adjacent
--    (start : V)
--    (priorState : dijkstra_search_state  g)
--    (stackHead : V)
--    (stackTail : List V):
--    WeightedDiGraph.search_invar_mother_is_adjacent start priorState → WeightedDiGraph.search_invar_mother_is_adjacent start (dijkstra_step_expand priorState stackHead stackTail) := by
--      intro mother_is_adjacent_prior
--      unfold WeightedDiGraph.search_invar_mother_is_adjacent
--      intro x
--      simp_all
--      intro x_not_start
--      unfold dijkstra_step_expand
--      simp_all
--      split
--      next adj_decide_true =>
--        split <;> split <;> grind
--      · next x_not_prior_visited => 
--        obtain ⟨ xx, x_in_new_visited ⟩ := x
--        unfold dijkstra_step_expand at x_in_new_visited
--        simp at x_in_new_visited
--        simp_all


-- stack is sorted by the path_order (i.e. distance) value
abbrev dijkstra_stack_sorted (s : dijkstra_search_state g) :=
  List.Pairwise (fun u v => s.pathOrder u ≺ s.pathOrder v) s.stack

  
set_option maxHeartbeats 1000000


/-- TODO: externalise haves into helpter theorems
--/ 
lemma dijkstra_expand_keeps_mother_ordered 
    (start : V)
    (priorState : dijkstra_search_state  g)
    (stackHead : V)
    (stackTail : List V):
    WeightedDiGraph.search_invar_mother_is_visited priorState ∧
      stackHead ∈ priorState.visited ∧ 
      WeightedDiGraph.search_invar_mother_decreasing_path_order start priorState
      ∧ WeightedDiGraph.search_invar_mother_is_visited priorState --dijkstra_stack_sorted priorState
      → WeightedDiGraph.search_invar_mother_decreasing_path_order start
          (dijkstra_step_expand priorState stackHead stackTail)
          := by
    intro ⟨mother_is_visited, stack_head_visited_prior, ⟨ mother_decreasing_prior, mother_visited⟩ ⟩  
    unfold WeightedDiGraph.search_invar_mother_decreasing_path_order
    intro a a_not_start
    obtain ⟨a,a_now_visited⟩ := a
    unfold FValueComp.lt
    unfold Nat.instFValueCompProd
    whnf
    apply toBoolUsing_eq_true
    apply Prod.lex_def.mpr
    apply Classical.or_iff_not_imp_left.mpr
    intro first_dim
    simp at first_dim
   

    -- local helper theorem
    have a_ne_visi_head_adj_a : a ∉ priorState.visited → g.Adj stackHead a := by
      intro a_not_visited
      unfold dijkstra_step_expand at a_now_visited
      grind

    have was_visited_if_not_adj : 
      ∀ x ∈ (dijkstra_step_expand priorState stackHead stackTail).visited, ¬ g.Adj stackHead x → x ∈ priorState.visited := by
      intro x now_visited not_adj
      unfold dijkstra_step_expand at now_visited
      grind

    have h_order : ∀ x : V, ¬ g.Adj stackHead x → priorState.pathOrder x = (dijkstra_step_expand priorState stackHead stackTail).pathOrder x := by 
      intro x ne_adj_head
      unfold dijkstra_step_expand
      grind

    have h_mother : ∀ x : (dijkstra_step_expand priorState stackHead stackTail).visited, ∀ ne_adj : ¬ g.Adj stackHead x, priorState.mother ⟨↑x, was_visited_if_not_adj x.val x.prop ne_adj ⟩ = (dijkstra_step_expand priorState stackHead stackTail).mother x := by 
      intro x ne_adj_head
      unfold dijkstra_step_expand
      grind
    
    have h_dec_1 :
      ∀ x ∈ priorState.visited, ((dijkstra_step_expand priorState stackHead stackTail).pathOrder x).1 ≤ (priorState.pathOrder x).1:= by 
      intro x
      unfold dijkstra_step_expand
      simp_all
      split_ifs <;> simp_all

    have h_dec_2 :
      ∀ x ∈ priorState.visited, ((dijkstra_step_expand priorState stackHead stackTail).pathOrder x).1 = (priorState.pathOrder x).1 → ((dijkstra_step_expand priorState stackHead stackTail).pathOrder x).2 ≤ (priorState.pathOrder x).2:= by 
      intro x
      unfold dijkstra_step_expand
      simp_all
      split_ifs <;> simp_all

    have h_new_visi :
      ∀ x : V, ∀ adj : g.Adj stackHead x, x ∉ priorState.visited → ((dijkstra_step_expand priorState stackHead stackTail).pathOrder x).1 ≤ (path_val priorState stackHead x adj).1:= by 
      intro x
      unfold dijkstra_step_expand
      simp_all
   
    have minvar : ∀ a_visited : a ∈ priorState.visited, (priorState.pathOrder (priorState.mother ⟨a, a_visited⟩)).1 ≤ (priorState.pathOrder a).1 := by
      intro a_visited
      unfold WeightedDiGraph.search_invar_mother_decreasing_path_order at mother_decreasing_prior
      specialize mother_decreasing_prior ⟨a,a_visited⟩ a_not_start
      unfold FValueComp.lt at mother_decreasing_prior
      unfold Nat.instFValueCompProd at mother_decreasing_prior
      grind

    have minvar_2 : ∀ a_visited : a ∈ priorState.visited, (priorState.pathOrder (priorState.mother ⟨a, a_visited⟩)).1 = (priorState.pathOrder a).1 → (priorState.pathOrder (priorState.mother ⟨a, a_visited⟩)).2 < (priorState.pathOrder a).2 := by
      intro a_visited eq_1
      unfold WeightedDiGraph.search_invar_mother_decreasing_path_order at mother_decreasing_prior
      specialize mother_decreasing_prior ⟨a,a_visited⟩ a_not_start
      unfold FValueComp.lt at mother_decreasing_prior
      unfold Nat.instFValueCompProd at mother_decreasing_prior
      grind

    have x_still_visited : ∀ x : priorState.visited, ↑x ∈ (dijkstra_step_expand priorState stackHead stackTail).visited := by 
      intro x
      unfold dijkstra_step_expand
      grind
    
    have mother_options : ∀ x : priorState.visited,
      ((dijkstra_step_expand priorState stackHead stackTail).mother ⟨x.val, x_still_visited x⟩) = stackHead ∨
      (((dijkstra_step_expand priorState stackHead stackTail).mother ⟨x.val, x_still_visited x⟩) = (priorState.mother x) ∧ (priorState.mother x) ≠ stackHead)
      := by 
        intro x
        unfold dijkstra_step_expand
        grind

    have mother_same_order : ∀ x : priorState.visited, ∀ adj_head_x : g.Adj stackHead x,
      ((dijkstra_step_expand priorState stackHead stackTail).mother ⟨x.val, x_still_visited x⟩) = (priorState.mother x) ∧ (priorState.mother x) ≠ stackHead →
      (dijkstra_step_expand priorState stackHead stackTail).pathOrder x = priorState.pathOrder x := by
        intro x adj_head_x mother_same
        unfold dijkstra_step_expand at mother_same ⊢
        grind


    have head_order_stays : ((dijkstra_step_expand priorState stackHead stackTail).pathOrder stackHead).1 = (priorState.pathOrder stackHead).1 := by
      unfold dijkstra_step_expand
      simp
      split_ifs
      · rfl
      · rfl
      · next h_1 h_2 =>
        grind
      · rfl

    by_cases adj_head_a : g.Adj stackHead a
    · 
      clear h_order h_mother
      apply a_a_imp_b_to_a_and_b
      and_intros
      · symm
        apply first_dim.antisymm
        clear first_dim
        by_cases a_visited : a ∈ priorState.visited
        · 
          specialize mother_options ⟨a, a_visited⟩
          cases mother_options
          · next mother_head =>
            rw [mother_head]
            rw [head_order_stays]  
            unfold dijkstra_step_expand at mother_head ⊢
            simp_all
            grind
          · next mother_same_and_not_head =>
            obtain ⟨ mother_same, mother_not_head ⟩ := mother_same_and_not_head
            rw [mother_same]
            --specialize mother_same_pre_path ⟨a,a_visited⟩ adj_head_a mother_same 
            specialize mother_same_order ⟨a,a_visited⟩ adj_head_a ⟨ mother_same, mother_not_head⟩  
            rw [mother_same_order]
            unfold dijkstra_step_expand at mother_same ⊢
            simp
            split_ifs <;> grind
        · unfold dijkstra_step_expand
          simp
          grind
      · 
        by_cases a_visited : a ∈ priorState.visited
        · intro eq
          specialize mother_options ⟨a, a_visited⟩
          cases mother_options
          · next mother_head =>
            rw [mother_head] at ⊢ eq
            unfold dijkstra_step_expand at mother_head eq ⊢
            simp_all
            grind
          · next mother_same_and_not_head =>
            obtain ⟨ mother_same, mother_not_head ⟩ := mother_same_and_not_head
            rw [mother_same] at ⊢ eq
            --specialize mother_same_pre_path ⟨a,a_visited⟩ adj_head_a mother_same 
            specialize mother_same_order ⟨a,a_visited⟩ adj_head_a ⟨ mother_same, mother_not_head⟩  
            rw [mother_same_order] at ⊢ eq
            unfold dijkstra_step_expand at mother_same eq ⊢
            simp at ⊢ eq
            split_ifs <;> grind
        · unfold dijkstra_step_expand
          simp
          grind
    · have a_visited : a ∈ priorState.visited := was_visited_if_not_adj a a_now_visited adj_head_a
      apply a_a_imp_b_to_a_and_b
      specialize h_order a adj_head_a
      rw [← h_order] at first_dim ⊢ 
      specialize h_mother ⟨a,a_now_visited⟩ adj_head_a
      rw [← h_mother] at first_dim ⊢

      and_intros
      · symm
        apply first_dim.antisymm
        clear first_dim
        apply le_trans
        · apply h_dec_1
          grind -- from mother visited invariant
        · grind
      · intro first_dim_eq
        clear first_dim
        apply lt_of_le_of_lt
        ·
          let m := priorState.mother ⟨a, a_visited⟩
          have m_visited : m ∈ priorState.visited := by grind
          have h_1 : ((dijkstra_step_expand priorState stackHead stackTail).pathOrder m).1 = (priorState.pathOrder m).1 := by grind
          specialize h_dec_2 m m_visited h_1
          apply h_dec_2
        · unfold WeightedDiGraph.search_invar_mother_decreasing_path_order at mother_decreasing_prior
          specialize mother_decreasing_prior ⟨a,a_visited⟩ a_not_start
          unfold FValueComp.lt at mother_decreasing_prior
          unfold Nat.instFValueCompProd at mother_decreasing_prior
          grind



------ Original proof for the first and case

    · --symm
      --apply first_dim.antisymm
      --clear first_dim -- has been used and is now irrelevant
      --unfold dijkstra_step_expand 
      --by_cases a_visited : a ∈ priorState.visited
      --· 
      --  have minvar : (priorState.pathOrder (priorState.mother ⟨a, a_visited⟩)).1 ≤ (priorState.pathOrder a).1 := by
      --    unfold WeightedDiGraph.search_invar_mother_decreasing_path_order at mother_decreasing_prior
      --    specialize mother_decreasing_prior ⟨a,a_visited⟩ a_not_start
      --    unfold FValueComp.lt at mother_decreasing_prior
      --    unfold Nat.instFValueCompProd at mother_decreasing_prior
      --    grind
      --  by_cases adj : g.Adj stackHead a
      --  · unfold edgeCost
      --    by_cases r :  (priorState.pathOrder a).1 < ((priorState.pathOrder stackHead).1 + g.Payload stackHead a adj, (priorState.pathOrder stackHead).2 + 1).1
      --    · by_cases adj_head_head : g.Adj stackHead stackHead
      --      all_goals
      --        by_cases adj_head_moterh : g.Adj stackHead (priorState.mother ⟨a, a_visited⟩) <;> (simp ; grind)
      --    · simp_all
      --      by_cases adj_head_moterh : g.Adj stackHead (priorState.mother ⟨a, a_visited⟩)
      --      all_goals
      --        by_cases update : (priorState.pathOrder a).1 =
      --                            (priorState.pathOrder stackHead).1 + g.Payload stackHead a adj ∧
      --                          (priorState.pathOrder a).2 < (priorState.pathOrder stackHead).2 + 1
      --        · grind
      --        · by_cases c : priorState.pathOrder a = ((priorState.pathOrder stackHead).1 + g.Payload stackHead a adj,(priorState.pathOrder stackHead).2 + 1)
      --          · grind 
      --          · by_cases adj_head_head : g.Adj stackHead stackHead <;> (simp_all ; grind)
      --  · -- a not adjacent to head
      --    --simp_all
      --    unfold edgeCost
      --    simp_all
      --    by_cases adj_head_moterh : g.Adj stackHead (priorState.mother ⟨a, a_visited⟩)
      --    all_goals
      --      grind
      --· -- have a was not visited but is now
      --  have head_adj_a : g.Adj stackHead a := a_ne_visi_head_adj_a a_visited
      --  by_cases adj : g.Adj stackHead stackHead
      --  · simp_all
      --    (split <;> try split) <;> grind
      --  · simp_all

------ END Original proof for the first and case
--      sorry
--    · unfold dijkstra_step_expand at first_dim ⊢
--      by_cases a_visited : a ∈ priorState.visited 
--      · specialize mother_decreasing_prior ⟨a,a_visited⟩ a_not_start
--        unfold FValueComp.lt at mother_decreasing_prior
--        unfold Nat.instFValueCompProd at mother_decreasing_prior
--        have geq : (priorState.pathOrder a).1 ≥ (priorState.pathOrder (priorState.mother ⟨a, a_visited⟩)).1 := by grind
--
--
--
--        unfold edgeCost at first_dim ⊢
--        by_cases adj : g.Adj stackHead a
--        · 
--          sorry
--          --simp
--          --by_cases leq : (priorState.pathOrder a).1 < (priorState.pathOrder stackHead).1 + g.Payload stackHead a adj
--          ----
--          --· --by_cases adj_head_mother : g.Adj stackHead (priorState.mother ⟨a, a_visited⟩)
--          --  · --by_cases adj_head_head : g.Adj stackHead stackHead
--          --    unfold edgeCost
--          --    by_cases baz : priorState.mother ⟨a, a_visited⟩ ∈ priorState.visited
--          --    · --simp_all
--          --      by_cases foo : (priorState.pathOrder a).1 =
--          --                        (priorState.pathOrder stackHead).1 + g.Payload stackHead a adj ∧
--          --                      (priorState.pathOrder a).2 < (priorState.pathOrder stackHead).2 + 1
--          --      · grind
--          --      · by_cases gak : priorState.pathOrder a = ((priorState.pathOrder stackHead).1 + g.Payload stackHead a adj, (priorState.pathOrder stackHead).2 + 1)--grind
--          --        · grind
--          --        · by_cases adj_head_mother : g.Adj stackHead (priorState.mother ⟨a, a_visited⟩)
--          --          · by_cases foo_mo : (priorState.pathOrder (priorState.mother ⟨a, a_visited⟩)).1 =
--          --                        (priorState.pathOrder stackHead).1 + g.Payload stackHead (priorState.mother ⟨a, a_visited⟩) adj_head_mother ∧
--          --                      (priorState.pathOrder (priorState.mother ⟨a, a_visited⟩)).2 < (priorState.pathOrder stackHead).2 + 1
-- 
--          --            · 
--          --              by_cases gak_mo : priorState.pathOrder (priorState.mother ⟨a, a_visited⟩) = ((priorState.pathOrder stackHead).1 + g.Payload stackHead (priorState.mother ⟨a, a_visited⟩) adj_head_mother, (priorState.pathOrder stackHead).2 + 1)--grind
--          --              · grind
--          --              · simp_all
--          --                sorry
--          --            · --grind
--          --              sorry
--          --          · grind (splits:=20)
--          --            simp
--          --            sorry
--          --    · grind
--          --· --simp_all
--          ----simp_all
--          --  --split
--          --  --· simp_all
--          --  --  have eq : (priorState.pathOrder a).1 = (priorState.pathOrder (priorState.mother ⟨a, a_visited⟩)).1 := by omega
--          --  --  simp_all
--          --  --  grind
--          --  --· split
--          --  --  · grind
--          --  --    sorry
--          --  --  · grind
--          --  --    sorry
--          --  sorry
--        · --by_cases adj_head_moterh : g.Adj stackHead (priorState.mother ⟨a, a_visited⟩)
--          --· simp_all
--          --  grind
--          --· simp_all
--          --  grind
--          sorry
--      · have adj : g.Adj stackHead a := a_ne_visi_head_adj_a a_visited
--        sorry
/--
    rw [Prod.lt_iff]
    

    and_intros
    · clear first_dim
      unfold dijkstra_step_expand
      by_cases a_visited : a ∈ priorState.visited
      · simp_all
        split
        · next contra => contradiction 
        · --next a_visited =>
          simp_all
          unfold edgeCost
          by_cases adj : g.Adj stackHead a
          · simp_all
            by_cases update : priorState.pathOrder a = new_cost priorState stackHead a adj  
            · simp_all
              by_cases head_adj_mother : g.Adj stackHead (priorState.mother ⟨ a, a_visited ⟩)
              · simp_all 
                unfold new_cost path_val edgeCost at update ⊢
                split
                · next p=>
                  split
                  · next q => 
                    simp at q p
                    by_cases r :  (priorState.pathOrder a).1 < ((priorState.pathOrder stackHead).1 + g.Payload stackHead a adj, (priorState.pathOrder stackHead).2 + 1).1
                    · 
                      omega
                      sorry
                    · grind
                  · split
                    · simp_all
                      omega
                      sorry
                    · omega
                      sorry
                · sorry
              · simp_all 
                sorry
            · simp_all
              unfold new_cost at update ⊢

              by_cases head_self_adj : g.Adj stackHead stackHead
              · simp_all
                split
                · next head_smaller =>
                  unfold path_val at head_smaller update ⊢
                  simp at head_smaller update ⊢
                  unfold edgeCost at head_smaller ⊢
                  obtain ⟨ cost_update, y, z⟩ := update

                  split
                  · next a_lt_head_edge =>
                    by_contra a_lt_head
                    simp_all 
                    omega
                  · split
                    · grind
                    · omega
                · next head_ge =>
                  unfold path_val at head_ge update ⊢
                  simp at update
                  obtain ⟨ cost_update, y, z⟩ := update
                  split
                  · next a_lt_head_plus =>
                    unfold edgeCost at head_ge a_lt_head_plus
                    split
                    · omega
                    · split <;> omega
                  · split <;> omega
              · simp_all 
                unfold path_val at update ⊢
                simp at update
                obtain ⟨ cost_update, y, z⟩ := update
                split
                · omega
                · split <;> omega
          · simp_all
            by_cases head_adj_mother : g.Adj stackHead (priorState.mother ⟨ a, a_visited ⟩)
            · simp_all 
              sorry
            · simp_all 
              sorry
      · simp_all
        by_cases head_self_adj : g.Adj stackHead stackHead <;> simp_all <;> grind
      --split
      --next adj_decide_true =>
      --  have adj : g.Adj stackHead ↑a := by grind
      --  by_cases a_visited : a ∈ priorState.visited
      --  · simp_all
      --    unfold edgeCost
      --    by_cases update : (priorState.pathOrder a).1 > (priorState.pathOrder stackHead).1 + g.Payload stackHead a adj
      --    · simp_all
      --      by_cases head_self_adj : g.Adj stackHead stackHead <;> simp_all <;> grind
      --    · simp_all
      --      and_intros
      --      · 
      --        by_cases head_adj_mother : g.Adj stackHead (priorState.mother ⟨ a, a_visited ⟩)
      --        · simp_all
      --          sorry
      --        · simp_all
      --          sorry
      --      · 
      --        by_cases head_adj_mother : g.Adj stackHead (priorState.mother ⟨ a, a_visited ⟩)
      --        · simp_all
      --          sorry
      --        · simp_all
      --          sorry
      --    


      --    --by_cases head_self_adj : g.Adj stackHead stackHead
      --    --· simp_all
      --    --  sorry
      --    --· simp_all
      --    --  sorry
      --  · simp_all
      --    by_cases head_self_adj : g.Adj stackHead stackHead <;> simp_all
    · sorry
    --  next adj_decide_false =>
    --    have a_was_visited : ↑a ∈ priorState.visited := by
    --      by_contra a_not_visited
    --      unfold dijkstra_step_expand at a_now_visited
    --      grind
    --    specialize mother_decreasing_prior a a_was_visited a_not_start
    --    rw [Prod.lt_iff] at mother_decreasing_prior
    --    by_cases head_adj_mother : g.Adj stackHead (priorState.mother ⟨ a, a_was_visited ⟩)
    --    · simp_all
    --      left
    --      cases mother_decreasing_prior
    --      · next mother_decreasing_prior => grind
    --      · next mother_decreasing_prior => apply mother_decreasing_prior.left
    --    · simp_all
    --      cases mother_decreasing_prior
    --      · next mother_decreasing_prior => grind
    --      · next mother_decreasing_prior => apply mother_decreasing_prior.left

    --· simp_all
    --  unfold dijkstra_step_expand at ⊢ first_dim
    --  split
    --  next adj_decide_true =>
    --    have adj : g.Adj stackHead ↑a := by grind
    --    by_cases a_was_visited : ↑a ∈ priorState.visited
    --    · sorry
    --    · sorry
    --    --· simp_all
    --    --  and_intros
    --    --  · --grind
    --    --    sorry
    --    --  · unfold edgeCost
    --    --    by_cases leq : priorState.pathOrder ↑a > priorState.pathOrder stackHead + g.Payload stackHead ↑a adj
    --    --    · simp_all
    --    --      sorry
    --    --    · grind
    --    --  · sorry
    --    --· simp_all
    --    --  unfold edgeCost
    --    --  --rw [WeightedDiGraph.payloadProofIrrelevant (h':=adj)]
    --    --  by_cases aa : (priorState.pathOrder ↑a).1 > (priorState.pathOrder stackHead).1 + g.Payload stackHead ↑a adj
    --    --  · simp_all
    --    --    aesop?
    --    --    sorry
    --    --  · simp_all
    --    --    sorry
    --  next adj_decide_false =>
    --    specialize mother_decreasing_prior ↑a a_was_visited a_not_start
    --    and_intros
    --    · sorry
    --    · sorry
     
      
/--

lemma dijkstra_expand_keeps_on_stack_or_all_neighbours_visited
    (priorState : dijkstra_search_state  g)
    (stackHead : V)
    (stackTail : List V):
     search_invar_on_stack_or_all_neighbours_visited priorState
     ∧ priorState.stack = (stackHead :: stackTail)
     → search_invar_on_stack_or_all_neighbours_visited  
          (dijkstra_step_expand priorState stackHead stackTail)
          := by
      intro ⟨ invar_holds_on_prior_state, stack_composition ⟩ 
      unfold search_invar_on_stack_or_all_neighbours_visited
      intro ⟨ x, x_now_on_stack⟩
      by_cases x_not_stack_head : x ≠ stackHead
      · by_cases x_was_not_in_stack_tail_: x ∈ stackTail
        · left
          unfold dijkstra_step_expand
          simp_all
        · by_cases x_not_visited : x ∉ priorState.visited
          · left
            unfold dijkstra_step_expand
            unfold dijkstra_step_expand at x_now_on_stack
            simp at x_now_on_stack
            simp_all
          · simp_all -- x was visited before and is not on the stack any more
            right
            intro y x_adj_y
            unfold dijkstra_step_expand
            simp_all
            left
            have x_invar := invar_holds_on_prior_state x
            simp_all
      · simp_all
        right
        intro y x_adj_y
        unfold dijkstra_step_expand
        simp_all
        by_cases h : y ∈ priorState.visited
        · left; exact h
        · right; left; exact h

lemma dijkstra_expand_keeps_start_visited
    (start : V)
    (priorState : dijkstra_search_state  g)
    (stackHead : V)
    (stackTail : List V):
     search_invar_start_visited start priorState →
     search_invar_start_visited start (dijkstra_step_expand priorState stackHead stackTail)
          := by
      intro pre_invar
      unfold dijkstra_step_expand
      unfold search_invar_start_visited 
      simp_all

lemma dijkstra_expand_visited_subset (priorState : dijkstra_search_state  g)
    (stackHead : V)
    (stackTail : List V):
    priorState.visited ⊆ (dijkstra_step_expand priorState stackHead stackTail).visited := by
    unfold dijkstra_step_expand
    simp_all

lemma dijkstra_expand_keeps_goal_on_stack :
   WeightedDiGraph.base_invar_carries_over_expand (state_type := dijkstra_search_state  g) goal dijkstra_step_expand  (search_prop_goal_on_stack (g:=g) goal):= by
    unfold WeightedDiGraph.base_invar_carries_over_expand
    intro s head tail ⟨ goal_prior_on_stack, head_not_goal, compose⟩ 
    change search_prop_goal_on_stack goal (dijkstra_step_expand s head tail)
    unfold dijkstra_step_expand
    unfold search_prop_goal_on_stack at ⊢ goal_prior_on_stack
    simp_all 
    cases  goal_prior_on_stack
    all_goals
      simp_all

lemma dijkstra_expand_goal_becomes_visited_puts_it_on_stack
  (goal : V)
  : 
  WeightedDiGraph.goal_becomes_visited_puts_it_on_stack (state_type := dijkstra_search_state  g) (g:=g) goal dijkstra_step_expand := by
    unfold WeightedDiGraph.goal_becomes_visited_puts_it_on_stack
    intro s head tail ⟨ a,b,c,d⟩ 
    change search_prop_goal_on_stack goal (dijkstra_step_expand s head tail)
    have bb : goal ∈ (dijkstra_step_expand s head tail).visited := b
    clear b
    unfold dijkstra_step_expand at bb ⊢
    unfold search_prop_goal_on_stack
    simp_all
    cases bb
    · contradiction
    · next h => right; exact h


lemma dijkstra_expand_keeps_base_invars:
  WeightedDiGraph.base_invar_carries_over_expand goal (state_type := dijkstra_search_state  g) dijkstra_step_expand (search_invar_all_basic (g:=g) start) := by
  unfold WeightedDiGraph.base_invar_carries_over_expand
  unfold search_invar_all_basic
  intro s head tail ⟨ ⟨ i1,i2,i3,i4,i5,i6⟩ , head_not_goal, compose⟩ 
  have head_is_visited : head ∈ s.visited := by
    apply i1
    rw [compose]
    simp
  and_intros
  · apply dijkstra_expand_keeps_stack_in_visited
    constructor
    · exact i1
    · constructor
      · exact head_is_visited 
      · intro x x_not_visited
        by_contra x_in_tail
        have x_on_stack : x ∈ (has_base_search_state.to_base_state (g:=g) s).stack := by
          rw [compose]
          simp_all
        apply i1 at x_on_stack
        contradiction 
  · apply dijkstra_expand_keeps_mother_in_visited
    constructor
    · exact i2
    · exact head_is_visited
  · apply dijkstra_expand_keeps_mother_is_adjacent
    exact i3
  · apply dijkstra_expand_keeps_mother_ordered
    constructor
    · exact i2
    · constructor
      · exact head_is_visited
      · exact i4
  · apply dijkstra_expand_keeps_on_stack_or_all_neighbours_visited
    constructor
    · exact i5 
    · exact compose 
  · apply dijkstra_expand_keeps_start_visited
    exact i6


def dijkstra (start : V) (goal : V): Option (g.Path start goal) :=
  let start_state := WeightedDiGraph.base_search_state_initial start ⟨0,0⟩
  have h : WeightedDiGraph.has_base_search_state.to_base_state (G:=g) start_state = base_search_state_initial start:= by simp_all only [start_state]; rfl

  WeightedDiGraph.search_exe_with_stack_step (g:=g) (start := start) (goal:=goal) (start_state:=start_state) (termination_metric := dijkstra_termination_metric) dijkstra_step_expand dijkstra_expand_metric_reduction dijkstra_expand_keeps_base_invars h 

--/
end NatGraph
