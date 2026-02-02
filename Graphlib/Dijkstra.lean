import Mathlib.Data.Bool.AllAny
import Mathlib.Data.FinEnum
import Mathlib.Data.Finset.Empty
import Mathlib.Data.List.MinMax
import Mathlib.Order.Basic
import Mathlib.Data.Multiset.DershowitzManna
import Mathlib.Data.Finsupp.WellFounded
import Mathlib.Data.List.ToFinsupp
import Mathlib.Algebra.Group.WithOne.Defs

import Graphlib.WF

import Graphlib.Lists
import Graphlib.FinEnum
import Graphlib.Basic
import Graphlib.NatGraph
import Graphlib.SearchState
import Graphlib.SearchAlgorithm
import Graphlib.SearchStep
import Init.SimpLemmas
import Init.Core

set_option trace.split.failure true
--set_option diagnostics true

-- def local global variable for a graph
variable {V : Type} [FinEnum V] [DecidableEq V]
variable {g : NatGraph V}


namespace Nat

@[simp]
def FValueLT (x y : ℕ × ℕ) : Prop := Prod.Lex (· < ·) (· < ·) x y

@[simp]
def FValueLT_B (x y : ℕ × ℕ) : Bool := Prod.Lex (· < ·) (· < ·) x y

instance : FValueComp (ℕ × ℕ) where
  lt := FValueLT
  lt_B := FValueLT_B
  wf := by
    unfold FValueLT
    apply Prod.Lex.instWellFoundedLTLex.wf
  lt_irr := by unfold FValueLT ; grind
  lt_trans := by unfold FValueLT ; grind
  lt_antisymm := by unfold FValueLT ; grind
  lt_sem_tot := by unfold FValueLT ; grind
  lt_B_eq := by simp


instance : DecidableRel FValueLT := by
  unfold FValueLT
  use inferInstance

end Nat


namespace NatGraph

open WeightedDiGraph


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
        (new_order a) = (new_order b) || FValueComp.lt_B (new_order a) (new_order b)) 
       
     WeightedDiGraph.base_search_state.mk new_visited new_order new_mother new_stack


def dijkstra_termination_metric 
    (s : dijkstra_search_state g): (Vector (WithTop (ℕ × ℕ)) g.nodeNum) × ℕ :=
    let l := (FinEnum.toList (Finset.univ : Finset V)).map  (fun v =>
      if v ∈ s.visited then WithTop.some (s.pathOrder v) else ⊤)

    let a := Array.mk l
    let v := Vector.mk a (by
      unfold WeightedDiGraph.nodeNum a l
      simp
      apply FinEnum.len_toList (α := V)
    )
    
    (v , s.stack.length)

--set_option trace.Meta.synthInstance true
--set_option pp.all true

lemma dijkstra_expand_metric_reduction : WeightedDiGraph.termination_proof_for_expand (G:=g) (state_type := dijkstra_search_state g) (D:=ℕ ×ℕ) (dijkstra_step_expand) goal dijkstra_termination_metric := by
    unfold WeightedDiGraph.termination_proof_for_expand
    intro state head tail ⟨head_ne_goal,compose⟩
    unfold WellFoundedRelation.rel
    unfold instWellFoundedRelationProdVectorWithTopNat_graphlib
    apply Prod.lex_iff.mpr
    apply (Classical.or_iff_not_imp_left).mpr
    contrapose
    rw [not_and]
    intro x
    by_cases eq : (dijkstra_termination_metric (dijkstra_step_expand state head tail)).1 = (dijkstra_termination_metric state).1
    · specialize x eq
      unfold dijkstra_termination_metric dijkstra_step_expand at x
      simp_all
      have stack_len : state.stack.length = tail.length + 1 := by
        clear eq x
        unfold WeightedDiGraph.has_base_search_state.to_base_state at compose
        unfold WeightedDiGraph.instHas_base_search_stateBase_search_state at compose 
        simp only at compose
        grind
      rw [stack_len] at x
      simp at x
      apply List.exists_mem_of_length_pos at x
      simp at x
      obtain ⟨v,⟨adj_head_v, prop_v⟩⟩ := x
      unfold dijkstra_step_expand dijkstra_termination_metric at eq
      simp at eq
      specialize eq v
      cases prop_v
      · simp_all
      · simp_all
        rename_i h
        obtain ⟨v_visi,v_not_in_tail, cost_update ⟩ := h
        specialize eq (le_of_lt cost_update)
        apply imp_iff_or_not.mp at eq
        cases eq <;> grind
    · clear x
      apply Vector.exists_ne_from_ne at eq
      obtain ⟨ i, prop_i ⟩ := eq
      by_contra not_lex
      apply List.not_Lex at not_lex
      cases not_lex
      case neg.inl all =>
        specialize all i
        grind
      case neg.inr pos =>
        clear i prop_i
        obtain ⟨i', ⟨ not_eq, not_lex, r⟩ ⟩ := pos
        clear r
        unfold dijkstra_termination_metric dijkstra_step_expand at not_lex not_eq
        unfold withTop.lex at not_lex
        simp at not_lex
        simp at not_eq
        have get_helper : i'.val < (FinEnum.toList (Finset.univ : Finset V)).length := by
          clear not_lex not_eq
          unfold WeightedDiGraph.nodeNum at i'
          convert i'.prop
          apply FinEnum.len_toList  
        --
        split at not_eq
        · split at not_eq
          · split at not_eq
            · split at not_eq 
              · simp at not_eq
              · simp_all
                split at not_lex
                · grind
                · rename_i h h' h'' 
                  obtain ⟨l,r⟩ := not_eq
                  simp at h''
                  apply imp_iff_or_not.mp at h''
                  cases h''
                  all_goals
                    next h''' =>
                    rw [Prod.lex_iff] at not_lex
                    simp only [Nat.lt_eq] at not_lex
                    grind
            · simp_all
          · split at not_eq <;> simp_all
        · split at not_eq
          · next h h' =>
            apply Finset.notMem_union.mp at h
            obtain ⟨ not_in, r ⟩ := h
            clear not_lex not_eq r
            simp_all
          · grind 



lemma dijkstra_expand_newly_added_are_adjacent 
    (priorState : dijkstra_search_state g)
    (stackHead : V)
    (stackTail : List V):
    ∀ x : V, x ∉ priorState.visited ∧ x ∉ stackTail ∧
      x ∈ (dijkstra_step_expand priorState stackHead stackTail).stack →  
      g.Adj stackHead x := by
    intro x ⟨x_not_visi, ⟨ x_not_on_stack_before, x_on_stack_after ⟩  ⟩
    unfold dijkstra_step_expand at x_on_stack_after
    simp_all


lemma dijkstra_expand_keeps_stack_in_visited 
    (priorState : dijkstra_search_state  g)
    (stackHead : V)
    (stackTail : List V):
    WeightedDiGraph.search_invar_stack_is_visited priorState ∧
      stackHead ∈ priorState.visited ∧ (∀ x : V, x ∉ priorState.visited → x ∉ stackTail) →
      WeightedDiGraph.search_invar_stack_is_visited (dijkstra_step_expand priorState stackHead stackTail) := by
      intro ⟨ stack_is_visited_prior, stackhead_visited, x_not_in_stack_tail⟩ 
      unfold WeightedDiGraph.search_invar_stack_is_visited
      intro x x_now_on_stack
      unfold dijkstra_step_expand
      simp_all
      by_cases x_was_visited : x ∈ priorState.visited
      · left
        exact x_was_visited
      · right
        have adj : g.Adj stackHead x := by 
          apply (dijkstra_expand_newly_added_are_adjacent priorState stackHead stackTail)
          simp_all
        use adj ; left ; exact x_was_visited


lemma dijkstra_expand_keeps_mother_in_visited 
    (priorState : dijkstra_search_state  g)
    (stackHead : V)
    (stackTail : List V):
    WeightedDiGraph.search_invar_mother_is_visited priorState ∧ stackHead ∈ priorState.visited → WeightedDiGraph.search_invar_mother_is_visited (dijkstra_step_expand priorState stackHead stackTail) := by
      intro mother_is_visited_prior
      unfold WeightedDiGraph.search_invar_mother_is_visited
      intro x
      by_cases mother_becomes_head : (dijkstra_step_expand priorState stackHead stackTail).mother x = stackHead
      · rw [mother_becomes_head]
        unfold dijkstra_step_expand
        simp_all
      · have x_was_visited : x.val ∈ priorState.visited := by
          obtain ⟨ x', x_now_visi ⟩ := x
          unfold dijkstra_step_expand at mother_becomes_head x_now_visi
          simp at x_now_visi
          cases x_now_visi
          · simp_all
          · simp_all
            rename_i h
            obtain ⟨ adj, p ⟩ := h
            cases p <;> simp_all
        have mother_unchanged : 
          (dijkstra_step_expand priorState stackHead stackTail).mother x = priorState.mother ⟨ x.val, x_was_visited ⟩ := by
          unfold dijkstra_step_expand at mother_becomes_head ⊢ 
          simp_all
        rw [mother_unchanged]
        unfold dijkstra_step_expand
        simp_all


lemma dijkstra_expand_keeps_mother_is_adjacent
    (start : V)
    (priorState : dijkstra_search_state  g)
    (stackHead : V)
    (stackTail : List V):
    WeightedDiGraph.search_invar_mother_is_adjacent start priorState → WeightedDiGraph.search_invar_mother_is_adjacent start (dijkstra_step_expand priorState stackHead stackTail) := by
      intro mother_is_adjacent_prior
      unfold WeightedDiGraph.search_invar_mother_is_adjacent
      intro x
      simp_all
      intro x_not_start
      unfold dijkstra_step_expand
      simp_all
      split
      next adj_decide_true =>
        split <;> split <;> grind
      · next x_not_prior_visited => 
        obtain ⟨ xx, x_in_new_visited ⟩ := x
        unfold dijkstra_step_expand at x_in_new_visited
        simp at x_in_new_visited
        simp_all



lemma dijkstra_mother_options
    (priorState : dijkstra_search_state  g)
    (stackHead : V)
    (stackTail : List V)
    (x : priorState.visited)
    (x_still_visited : x.val ∈ (dijkstra_step_expand priorState stackHead stackTail).visited):
      ((dijkstra_step_expand priorState stackHead stackTail).mother ⟨x.val, x_still_visited⟩) = stackHead ∨
      (((dijkstra_step_expand priorState stackHead stackTail).mother ⟨x.val, x_still_visited⟩) = (priorState.mother x) ∧ (priorState.mother x) ≠ stackHead)
      := by 
        unfold dijkstra_step_expand
        grind


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
      ∧ WeightedDiGraph.search_invar_mother_is_visited priorState 
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
    --apply toBoolUsing_eq_true
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
      simp at mother_decreasing_prior
      grind

    have minvar_2 : ∀ a_visited : a ∈ priorState.visited, (priorState.pathOrder (priorState.mother ⟨a, a_visited⟩)).1 = (priorState.pathOrder a).1 → (priorState.pathOrder (priorState.mother ⟨a, a_visited⟩)).2 < (priorState.pathOrder a).2 := by
      intro a_visited eq_1
      unfold WeightedDiGraph.search_invar_mother_decreasing_path_order at mother_decreasing_prior
      specialize mother_decreasing_prior ⟨a,a_visited⟩ a_not_start
      unfold FValueComp.lt at mother_decreasing_prior
      unfold Nat.instFValueCompProd at mother_decreasing_prior
      simp at mother_decreasing_prior
      grind

    have x_still_visited : ∀ x : priorState.visited, ↑x ∈ (dijkstra_step_expand priorState stackHead stackTail).visited := by 
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
          have mother_options := dijkstra_mother_options priorState stackHead stackTail ⟨ a, a_visited⟩ (x_still_visited ⟨ a, a_visited⟩)
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
          have mother_options := dijkstra_mother_options priorState stackHead stackTail ⟨ a, a_visited⟩ (x_still_visited ⟨ a, a_visited⟩)
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

      

lemma dijkstra_expand_keeps_on_stack_or_all_neighbours_visited
    (priorState : dijkstra_search_state  g)
    (stackHead : V)
    (stackTail : List V):
     WeightedDiGraph.search_invar_on_stack_or_all_neighbours_visited priorState
     ∧ priorState.stack = (stackHead :: stackTail)
     → WeightedDiGraph.search_invar_on_stack_or_all_neighbours_visited  
          (dijkstra_step_expand priorState stackHead stackTail)
          := by
      intro ⟨ invar_holds_on_prior_state, stack_composition ⟩ 
      unfold WeightedDiGraph.search_invar_on_stack_or_all_neighbours_visited
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
     WeightedDiGraph.search_invar_start_visited start priorState →
     WeightedDiGraph.search_invar_start_visited start (dijkstra_step_expand priorState stackHead stackTail)
          := by
      intro pre_invar
      unfold dijkstra_step_expand
      unfold WeightedDiGraph.search_invar_start_visited 
      simp_all

lemma dijkstra_expand_visited_subset (priorState : dijkstra_search_state  g)
    (stackHead : V)
    (stackTail : List V):
    priorState.visited ⊆ (dijkstra_step_expand priorState stackHead stackTail).visited := by
    unfold dijkstra_step_expand
    simp_all

lemma dijkstra_expand_keeps_goal_on_stack :
   WeightedDiGraph.base_invar_carries_over_expand (state_type := dijkstra_search_state g) dijkstra_step_expand goal (WeightedDiGraph.search_prop_goal_on_stack (G:=g) (D:=ℕ × ℕ) goal):= by
    unfold WeightedDiGraph.base_invar_carries_over_expand
    intro s head tail ⟨ goal_prior_on_stack, head_not_goal, compose⟩ 
    change WeightedDiGraph.search_prop_goal_on_stack goal (dijkstra_step_expand s head tail)
    unfold dijkstra_step_expand
    unfold WeightedDiGraph.search_prop_goal_on_stack at ⊢ goal_prior_on_stack
    simp_all 
    cases  goal_prior_on_stack
    all_goals
      simp_all

lemma dijkstra_expand_goal_becomes_visited_puts_it_on_stack
  (goal : V)
  : 
  WeightedDiGraph.goal_becomes_visited_puts_it_on_stack (state_type := dijkstra_search_state g) (G:=g) (D:=ℕ×ℕ) dijkstra_step_expand goal := by
    unfold WeightedDiGraph.goal_becomes_visited_puts_it_on_stack
    intro s head tail ⟨ a,b,c,d⟩ 
    change WeightedDiGraph.search_prop_goal_on_stack goal (dijkstra_step_expand s head tail)
    have bb : goal ∈ (dijkstra_step_expand s head tail).visited := b
    clear b
    unfold dijkstra_step_expand at bb ⊢
    unfold WeightedDiGraph.search_prop_goal_on_stack
    simp_all
    cases bb
    · contradiction
    · next h => right; exact h


lemma dijkstra_expand_keeps_base_invars:
  WeightedDiGraph.base_invar_carries_over_expand (state_type := dijkstra_search_state  g) dijkstra_step_expand goal (WeightedDiGraph.search_invar_all_basic (G:=g) (D:=ℕ×ℕ) start) := by
  unfold WeightedDiGraph.base_invar_carries_over_expand
  unfold WeightedDiGraph.search_invar_all_basic
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
        have x_on_stack : x ∈ (WeightedDiGraph.has_base_search_state.to_base_state (G:=g) (D:=ℕ×ℕ) s).stack := by
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
      · and_intros
        · exact i4
        · exact i2
  · apply dijkstra_expand_keeps_on_stack_or_all_neighbours_visited
    constructor
    · exact i5 
    · exact compose 
  · apply dijkstra_expand_keeps_start_visited
    exact i6


def dijkstra (start : V) (goal : V): Option (g.Path start goal) :=
  let start_state := WeightedDiGraph.base_search_state_initial start ⟨0,0⟩
  have h : WeightedDiGraph.has_base_search_state.to_base_state (G:=g) start_state = WeightedDiGraph.base_search_state_initial start (0,0):= by simp_all only [start_state]; rfl

  WeightedDiGraph.search_exe_with_stack_step (G:=g) (start := start) (goal:=goal) (start_state:=start_state) (termination_metric := dijkstra_termination_metric) dijkstra_step_expand dijkstra_expand_metric_reduction dijkstra_expand_keeps_base_invars h 


def dijkstra_last_state (start : V) (goal : V): WeightedDiGraph.base_search_state g (ℕ×ℕ) × Bool :=
  WeightedDiGraph.search_with_stack_step (goal:=goal) (start_state := WeightedDiGraph.base_search_state_initial start (0,0)) dijkstra_step_expand dijkstra_expand_metric_reduction


theorem dijkstra_is_sound (start : V) (goal : V) :
    (Option.isSome (dijkstra (g:=g) start goal) → (∃ x : (g.Path start goal), x = x)) := by
  apply WeightedDiGraph.search_with_stack_step_is_sound
  · apply dijkstra_expand_metric_reduction
  · apply dijkstra_expand_keeps_base_invars
  · rfl



theorem dijkstra_is_complete (start : V) (goal : V):
    ((∃ x : (g.Path start goal), x = x) → Option.isSome (dijkstra (g:=g) start goal)) := by
  apply WeightedDiGraph.search_with_stack_step_is_complete
  · apply dijkstra_expand_metric_reduction
  · apply dijkstra_expand_keeps_base_invars
  · rfl
  · apply dijkstra_expand_keeps_goal_on_stack
  · apply dijkstra_expand_goal_becomes_visited_puts_it_on_stack

/--Invars for Dijkstra-/

abbrev dijkstra_invar_on_stack_or_all_neighbours_max_order (s : WeightedDiGraph.base_search_state g (ℕ×ℕ)):=
  ∀ x : s.visited, ↑x ∉ s.stack → ∀ y : V, (adj : g.Adj x y) → (s.pathOrder y).1 ≤ (s.pathOrder x).1 + g.edgeCost adj 

/-- The differene in path order between a node an its mother corresponds to the cost of the edge between them. The mother however might have an even *lower* path order if it has been updated, but that update has not been propagated to the child yet -/
abbrev dijkstra_path_order_diff_by_edge_cost (start : V) (s : WeightedDiGraph.base_search_state g (ℕ×ℕ)) :=
    ∀ mother_invar_adj : WeightedDiGraph.search_invar_mother_is_adjacent start s,
    ∀ u : V, (h : u ∈ s.visited) → (ne_start : u ≠ start) →
      (s.pathOrder u).1 ≥ (s.pathOrder (s.mother ⟨u,h⟩)).1 + 
        g.edgeCost (mother_invar_adj ⟨u,h⟩ ne_start)

/-- The differene in path order between a node an its mother corresponds to the difference in path length between them. The mother however might have an even *lower* path order if it has been updated, but that update has not been propagated to the child yet -/
abbrev dijkstra_path_order_diff_by_one (start : V) (s : WeightedDiGraph.base_search_state g (ℕ×ℕ)) :=
    ∀ u : V, (h : u ∈ s.visited) → (ne_start : u ≠ start) →
      (s.pathOrder u).2 ≥ (s.pathOrder (s.mother ⟨u,h⟩)).2 + 1


-- stack is sorted by the path_order (i.e. distance) value
abbrev dijkstra_stack_sorted (s : WeightedDiGraph.base_search_state g (ℕ×ℕ)) :=
  List.Pairwise (fun u v => (s.pathOrder u = s.pathOrder v) ∨ (s.pathOrder u ≺ s.pathOrder v)) s.stack



-- 
abbrev dijkstra_stack_shortest_path (start : V) (s : WeightedDiGraph.base_search_state g (ℕ×ℕ)) :=
  ∀ u ∈ s.visited, u ∉ s.stack ∨ (if ne : s.stack ≠ [] then s.stack.head ne = u else false) →
    g.cost_is start u (s.pathOrder u).1
  --∨ (
  --  -- u could be the head of the stack
  --  ∀ p : g.Path start u, p.is_cheapest → (p.support ∩ s.stack) \ {u} ≠ ∅
  --))


@[simp]
abbrev search_invar_start_path_order_zero_zero (start : V) (s : WeightedDiGraph.base_search_state g (ℕ×ℕ)) :=
      s.pathOrder start = (0,0)


abbrev dijkstra_all_invar (start : V) (s : WeightedDiGraph.base_search_state g (ℕ×ℕ)) :=
      WeightedDiGraph.search_invar_all_basic start s
    ∧ dijkstra_stack_shortest_path start s
    ∧ dijkstra_path_order_diff_by_edge_cost start s
    ∧ dijkstra_invar_on_stack_or_all_neighbours_max_order s
    ∧ dijkstra_stack_sorted s
    ∧ search_invar_start_path_order_zero_zero start s



omit [DecidableEq V] in
lemma dijkstra_invar_holds_at_init (start : V):
      dijkstra_all_invar start (WeightedDiGraph.base_search_state_initial (G:=g) start (0,0)) := by
      constructor
      · apply WeightedDiGraph.base_search_state_initial_all_basic_invars
      · and_intros
        · unfold dijkstra_stack_shortest_path
          unfold WeightedDiGraph.base_search_state_initial
          unfold cost_is
          simp
          use g.nil_path start
          unfold WeightedDiGraph.Path.is_cheapest
          and_intros
          · apply WeightedDiGraph.Path.cost_nil_zero
          · simp
            intro a nodup
            rw [← WeightedDiGraph.Path.cost]
            rw [WeightedDiGraph.Path.cost_nil_zero]
            simp_all
        · unfold dijkstra_path_order_diff_by_edge_cost
          unfold WeightedDiGraph.base_search_state_initial
          simp
          intro u u_is_start u_ne_start
          grind
        · unfold dijkstra_invar_on_stack_or_all_neighbours_max_order
          unfold WeightedDiGraph.base_search_state_initial
          simp
        · unfold dijkstra_stack_sorted
          unfold WeightedDiGraph.base_search_state_initial
          simp
        · unfold search_invar_start_path_order_zero_zero
          unfold WeightedDiGraph.base_search_state_initial
          simp


section
variable (state : WeightedDiGraph.base_search_state g (ℕ×ℕ))

lemma dijkstra_expand_keeps_shortest_path_invar
    (start : V) (goal : V)
    ----- co-invariants needed for path extraction
    (mother_invar : WeightedDiGraph.search_invar_mother_is_visited state)
    (mother_invar_adj : WeightedDiGraph.search_invar_mother_is_adjacent start state)
    (decreasing_invar : WeightedDiGraph.search_invar_mother_decreasing_path_order start state)
    (start_visited : WeightedDiGraph.search_invar_start_visited start state)
    (on_stack_or_nei_visited : WeightedDiGraph.search_invar_on_stack_or_all_neighbours_visited state)
    (stack_visited_invar : WeightedDiGraph.search_invar_stack_is_visited state)
    -- new bfs_ specific invars
    (path_order_diff : dijkstra_path_order_diff_by_edge_cost start state)
    --(extract_length_invar : dijkstra_path_as_extracted_as_long_as_sort_index start state)
    (update_invar : dijkstra_invar_on_stack_or_all_neighbours_max_order state)
    (stack_sorted : dijkstra_stack_sorted state)
    (start_path_order : search_invar_start_path_order_zero_zero start state)
    :
     ∀ head : V, ∀ tail : List V, 
        dijkstra_stack_shortest_path start state
          ∧ ¬ head = goal
          ∧ state.stack = head :: tail
        → dijkstra_stack_shortest_path start (dijkstra_step_expand state head tail) := by
  sorry



lemma dijkstra_path_extracted_not_longer_than_path_order (start : V) (s : WeightedDiGraph.base_search_state g (ℕ×ℕ))
    (mother_invar : search_invar_mother_is_visited  s)
    (mother_invar_adj : search_invar_mother_is_adjacent start s)
    (decreasing_invar : search_invar_mother_decreasing_path_order start s)
    (diff_invar : dijkstra_path_order_diff_by_edge_cost start s)
    (u : V)
    (u_visited : u ∈ s.visited):
    (WeightedDiGraph.extract_path_to start u s u_visited mother_invar mother_invar_adj decreasing_invar).1.cost ≤ (s.pathOrder u).1 := by
    by_cases u_ne_start : u ≠ start
    · unfold extract_path_to
      simp
      split
      · rename_i u_eq_start
        contradiction
      · have d := diff_invar mother_invar_adj u u_visited u_ne_start
        apply le_trans
        rotate_left
        · apply d
        · simp_all
          rw [← Path.cost_same]
          rw [Path.concat_inc_cost_by_edge]
          conv =>
            right
            rw [add_comm]
          unfold edgeCost
          apply Nat.add_le_add_left
          apply dijkstra_path_extracted_not_longer_than_path_order
          apply diff_invar
    · simp at u_ne_start
      subst u_ne_start
      unfold extract_path_to
      simp_all
      unfold Walk.cost
      simp 
termination_by FValueComp.wf.wrap (s.pathOrder u)
decreasing_by
  apply decreasing_invar
  simp_all

  

lemma dijkstra_expand_keeps_on_path_order_diff(start goal : V)
    (stack_visited_invar : WeightedDiGraph.search_invar_stack_is_visited state)
    (mother_invar_adj : search_invar_mother_is_adjacent start state)
    (mother_invar : search_invar_mother_is_visited state)
    :
     ∀ head : V, ∀ tail : List V, 
        dijkstra_path_order_diff_by_edge_cost start state
          ∧ head ≠ goal
          ∧ state.stack = head :: tail
        → dijkstra_path_order_diff_by_edge_cost start (dijkstra_step_expand state head tail) := by
  intro head tail ⟨prior_diff,head_ne_goal,compose⟩ 
  unfold dijkstra_path_order_diff_by_edge_cost
  intro now_mother_adj_invar u u_now_visited head_ne_start
  by_cases u_visited : u ∈ state.visited
  · 
    have mother_options := dijkstra_mother_options state head tail ⟨u,u_visited⟩ u_now_visited
    cases mother_options
    case pos.inl mother_head =>
      simp at mother_head
      conv =>
        right
        arg 1
        rw [mother_head]
      unfold dijkstra_step_expand at ⊢ mother_head
      unfold dijkstra_path_order_diff_by_edge_cost at prior_diff
      specialize prior_diff mother_invar_adj u
      
      by_cases adj_head_u : g.Adj head u <;> by_cases adj_head_head : g.Adj head head <;> (simp_all ; try grind)
    case pos.inr ne_mother =>
      obtain ⟨mother_same,mother_ne_head⟩ := ne_mother
      simp at mother_same
      conv =>
        right
        arg 1
        rw [mother_same]
      unfold dijkstra_path_order_diff_by_edge_cost at prior_diff
      specialize prior_diff mother_invar_adj u
      unfold search_invar_mother_is_visited at mother_invar
      specialize mother_invar ⟨u,u_visited⟩
      unfold dijkstra_step_expand
      unfold dijkstra_step_expand at mother_same
      by_cases adj_head_u : g.Adj head u <;> by_cases adj_head_mother : g.Adj head (state.mother ⟨u, u_visited⟩) <;> (simp_all ; try grind)
  · have adj_head_u : g.Adj head u := by
      unfold dijkstra_step_expand at u_now_visited
      simp_all
    unfold dijkstra_step_expand
    simp_all
    by_cases adj_head_head : g.Adj head head
    · simp_all
      split <;> simp_all
    · simp_all

lemma dijkstra_expand_keeps_on_stack_or_nei_max_order(goal : V)
    (on_stack_or_nei_visited : WeightedDiGraph.search_invar_on_stack_or_all_neighbours_visited state)
    :
     ∀ head : V, ∀ tail : List V, 
        dijkstra_invar_on_stack_or_all_neighbours_max_order  state
          ∧ head ≠ goal
          ∧ state.stack = head :: tail
        → dijkstra_invar_on_stack_or_all_neighbours_max_order  (dijkstra_step_expand state head tail) := by
      unfold dijkstra_invar_on_stack_or_all_neighbours_max_order
      simp
      intro head tail prior_invar head_ne_goal compose a a_visited_after a_not_on_stack_after y a_adj_y

      unfold dijkstra_step_expand at a_visited_after a_not_on_stack_after
      simp at a_visited_after a_not_on_stack_after
      obtain ⟨ a_not_in_tail, a_visi_if_head_adj ⟩ := a_not_on_stack_after
      cases a_visited_after
      · next a_visited_before =>
        by_cases a_eq_head : a = head
        · subst a_eq_head
          by_cases y_visited_before : y ∈ state.visited
          · unfold dijkstra_step_expand
            simp [y_visited_before, a_visited_before]
            split_ifs <;> grind 
          · unfold dijkstra_step_expand
            simp [y_visited_before, a_visited_before]
            grind
        · by_cases y_visited_before : y ∈ state.visited
          · unfold dijkstra_step_expand
            simp [y_visited_before, a_visited_before]
            split_ifs <;> grind 
          · unfold dijkstra_step_expand
            simp [y_visited_before, a_visited_before]
            split <;> (simp_all ; grind)
      · next both =>
        obtain ⟨ head_adj_a, a_ne_visited ⟩ := both
        grind -- contradictory


lemma merge_two_prop {α : Type} (le1 : α → α → Prop) (le2 : α → α → Bool)
  (trans : ∀ (a b c : α), le2 a b = true → le2 b c = true → le2 a c = true)
  (total : ∀ (a b : α), (le2 a b || le2 b a) = true)
  (le_eq : le1 = (fun x y => le2 x y = true))
  (l : List α):
  List.Pairwise le1 (l.mergeSort le2) := by
    subst le_eq
    apply List.pairwise_mergeSort
    all_goals
      grind

lemma  dijkstra_merge_trans [FValueComp (ℕ×ℕ)] (a b c : ℕ × ℕ)
  (a_b : a = b || FValueComp.lt_B a b)
  (b_c : b = c || FValueComp.lt_B b c) : 
  a = c || FValueComp.lt_B a c := by
  by_cases a_eq_b : a = b <;> by_cases b_eq_c : b = c
  · simp_all
  · simp_all
  · simp_all
  · simp_all
    repeat rw [← FValueComp.lt_B_eq] at a_b b_c ⊢
    right
    apply FValueComp.lt_trans
    · exact a_b
    · exact b_c

lemma  dijkstra_merge_total [FValueComp (ℕ×ℕ)] (a b: ℕ × ℕ): 
  (a = b || FValueComp.lt_B a b) || (b = a || FValueComp.lt_B b a) := by
  by_cases a_eq_b : a = b
  · grind
  · simp_all
    have h := FValueComp.lt_sem_tot a b a_eq_b
    repeat rw [← FValueComp.lt_B_eq]
    cases h
    case neg.inl f => left ; exact f
    case neg.inr f => right ; right ; exact f


lemma dijkstra_expand_keeps_stack_sorted(goal : V)
    :
     ∀ head : V, ∀ tail : List V, 
        dijkstra_stack_sorted  state
          ∧ head ≠ goal
          ∧ state.stack = head :: tail
        → dijkstra_stack_sorted  (dijkstra_step_expand state head tail) := by
      intro head tail ⟨ prior_invar,head_ne_goal,compose⟩ 
      unfold dijkstra_stack_sorted
      unfold dijkstra_step_expand
      apply merge_two_prop 
      · intro a b c a_b b_c
        apply dijkstra_merge_trans
        · apply a_b
        · apply b_c
      · intro a b
        apply dijkstra_merge_total
      · ext x y
        rw [FValueComp.lt_B_eq]
        simp


lemma dijkstra_expand_start_path_order_zero_carries (start : V) (goal : V)
    (start_visited : WeightedDiGraph.search_invar_start_visited start state)
    :
     ∀ head : V, ∀ tail : List V, 
        search_invar_start_path_order_zero_zero start state
          ∧ ¬ head = goal
          ∧ state.stack = head :: tail
        → search_invar_start_path_order_zero_zero start (dijkstra_step_expand state head tail) := by
      intro head tail ⟨ prior_invar,head_ne_goal,compose⟩ 
      unfold search_invar_start_path_order_zero_zero
      unfold dijkstra_step_expand
      simp_all


end 

lemma dijkstra_expand_carries_all_dijkstra_invars (start : V) (goal : V):
      WeightedDiGraph.base_invar_carries_over_expand (dijkstra_step_expand (g:=g)) goal (dijkstra_all_invar (g:=g)  start) := by
      unfold WeightedDiGraph.base_invar_carries_over_expand
      intro s head tail ⟨ invar_before, head_ne_goal, compose⟩ 
      unfold dijkstra_all_invar
      constructor
      · apply dijkstra_expand_keeps_base_invars
        · exact ⟨ invar_before.left, head_ne_goal, compose⟩
      · and_intros
        · apply dijkstra_expand_keeps_shortest_path_invar
          · exact invar_before.left.right.left
          · exact invar_before.left.right.right.left
          · exact invar_before.left.right.right.right.left
          · exact invar_before.left.right.right.right.right.right
          · exact invar_before.left.right.right.right.right.left
          · exact invar_before.left.left
          · exact invar_before.right.right.left
          · exact invar_before.right.right.right.left
          · exact invar_before.right.right.right.right.left
          · exact invar_before.right.right.right.right.right
          · exact ⟨ invar_before.right.left, head_ne_goal, compose⟩
        · apply dijkstra_expand_keeps_on_path_order_diff 
          · exact invar_before.left.left
          · exact invar_before.left.right.right.left
          · exact invar_before.left.right.left
          · exact ⟨ invar_before.right.right.left, head_ne_goal, compose⟩
        · apply dijkstra_expand_keeps_on_stack_or_nei_max_order
          · exact invar_before.left.right.right.right.right.left
          · exact ⟨ invar_before.right.right.right.left, head_ne_goal, compose⟩
        · apply dijkstra_expand_keeps_stack_sorted
          · exact ⟨ invar_before.right.right.right.right.left, head_ne_goal, compose⟩
        · apply dijkstra_expand_start_path_order_zero_carries
          · exact invar_before.left.right.right.right.right.right
          · exact ⟨ invar_before.right.right.right.right.right, head_ne_goal, compose⟩



/- -/
theorem dijkstra_is_optimal (start : V) (goal : V)
    (returned_path : Option.isSome (dijkstra (g:=g) start goal)):
    ((dijkstra (g:=g) start goal).get returned_path).is_cheapest := by
    let final : WeightedDiGraph.base_search_state g (ℕ×ℕ) × Bool := WeightedDiGraph.search_with_stack_step (goal:=goal) (start_state := WeightedDiGraph.base_search_state_initial start (0,0)) (dijkstra_step_expand) dijkstra_expand_metric_reduction
    let final_state := final.1
 
    -- general properties
    have h_4 : WeightedDiGraph.search_prop_stack_head_is_goal goal final_state := by
      --intro terminated_with_goal_found 
      --unfold search_prop_stack_head_is_goal
      unfold final_state
      unfold final
      unfold WeightedDiGraph.search_with_stack_step
      simp
      unfold WeightedDiGraph.search_internal
      apply WeightedDiGraph.search_recurse_obtain_base_termination_property (G:=g) (D:=ℕ×ℕ) (T:=(Vector (WithTop (ℕ × ℕ)) g.nodeNum) × ℕ) goal (WeightedDiGraph.base_search_state_initial start (0,0)) (property_after_termination := WeightedDiGraph.search_prop_stack_head_is_goal (D:=ℕ×ℕ) goal ) (terminated_with := true) (search_step := WeightedDiGraph.search_stack_step (G:=g) (D:=ℕ×ℕ) (dijkstra_step_expand (g:=g))) dijkstra_termination_metric 
      · intro s
        apply WeightedDiGraph.search_stack_step_goal_stack_head_if_terminated
      · unfold dijkstra at returned_path
        unfold WeightedDiGraph.search_exe_with_stack_step at returned_path
        unfold WeightedDiGraph.search_exe at returned_path
        simp_all
        apply returned_path

    have t_0 : WeightedDiGraph.search_invar_stack_is_visited final_state := by
      unfold final_state
      unfold final
      unfold WeightedDiGraph.search_with_stack_step
      simp only []
      apply WeightedDiGraph.search_returns_with_stack_visited (state_type := WeightedDiGraph.base_search_state g (ℕ×ℕ)) (start_state := WeightedDiGraph.base_search_state_initial start (0,0)) (start := start)
      · rfl
      · apply WeightedDiGraph.base_invar_carries_over_stack_step
        apply dijkstra_expand_keeps_base_invars

    have h_3 : WeightedDiGraph.search_prop_goal_visited goal final_state := by
      apply t_0
      unfold WeightedDiGraph.search_prop_stack_head_is_goal at h_4 
      apply List.eq_cons_of_mem_head? at h_4
      rw [h_4]
      simp

    have t_1 : WeightedDiGraph.search_invar_mother_is_visited final_state := by
      unfold final_state
      unfold final
      unfold WeightedDiGraph.search_with_stack_step
      simp only []
      apply WeightedDiGraph.search_returns_with_mother_visited (state_type := WeightedDiGraph.base_search_state g (ℕ×ℕ)) (start_state := WeightedDiGraph.base_search_state_initial start (0,0)) (start := start)
      · rfl
      · apply WeightedDiGraph.base_invar_carries_over_stack_step
        apply dijkstra_expand_keeps_base_invars

    have t_2 : WeightedDiGraph.search_invar_mother_is_adjacent start final_state := by
      unfold final_state
      unfold final
      unfold WeightedDiGraph.search_with_stack_step
      simp only []
      apply WeightedDiGraph.search_returns_with_mother_adjacent (state_type := WeightedDiGraph.base_search_state g (ℕ×ℕ)) (start_state := WeightedDiGraph.base_search_state_initial start (0,0)) (start := start)
      · rfl
      · apply WeightedDiGraph.base_invar_carries_over_stack_step
        apply dijkstra_expand_keeps_base_invars

    have t_3 : WeightedDiGraph.search_invar_mother_decreasing_path_order start final_state := by
      unfold final_state
      unfold final
      unfold WeightedDiGraph.search_with_stack_step
      simp only []
      apply WeightedDiGraph.search_returns_with_mother_decreasing (state_type := WeightedDiGraph.base_search_state g (ℕ×ℕ)) (start_state := WeightedDiGraph.base_search_state_initial start (0,0)) (start := start)
      · rfl
      · apply WeightedDiGraph.base_invar_carries_over_stack_step
        apply dijkstra_expand_keeps_base_invars


    -- Dijkstra specific ones
    have dijkstra_full_invar_at_end : dijkstra_all_invar start final_state := by
     have right_class : (fun s => dijkstra_all_invar start (WeightedDiGraph.has_base_search_state.to_base_state (G:=g) s)) final_state := by
      unfold final_state
      unfold final
      unfold WeightedDiGraph.search_with_stack_step
      unfold WeightedDiGraph.search_internal
      simp
      apply WeightedDiGraph.search_recurse_lift_base_invariant 
      constructor
      · apply dijkstra_invar_holds_at_init
      · apply WeightedDiGraph.base_invar_carries_over_stack_step
        apply dijkstra_expand_carries_all_dijkstra_invars 
     -- needs to be applied, lean4 has problems with they type-class here
     apply right_class

    have i_1 : dijkstra_stack_shortest_path start final_state := dijkstra_full_invar_at_end.2.1

    --have h_2 : dijkstra_path_as_extracted_as_long_as_sort_index start final_state := dijkstra_full_invar_at_end.2.2.1


    have h : g.cost_is start goal (final_state.pathOrder goal).1 := by
     have i_1' := i_1 goal h_3
     unfold WeightedDiGraph.search_prop_stack_head_is_goal at h_4
     apply i_1'
     right
     obtain ⟨ tail, compose ⟩ := List.head?_eq_some_iff.mp h_4
     simp_all


    unfold dijkstra
    unfold WeightedDiGraph.search_exe_with_stack_step
    unfold WeightedDiGraph.search_exe
    unfold WeightedDiGraph.Path.is_cheapest
    intro p'
    unfold WeightedDiGraph.distance_is at h 
    obtain ⟨p, ⟨ p_path_length, p_is_cheapest ⟩ ⟩  := h

    --unfold dijkstra_path_as_extracted_as_long_as_sort_index at h_2
    have prop := dijkstra_path_extracted_not_longer_than_path_order start final_state t_1 t_2 t_3 dijkstra_full_invar_at_end.2.2.1
    unfold final_state at prop
    unfold final at prop
    unfold WeightedDiGraph.search_with_stack_step at prop
    simp_all
    unfold WeightedDiGraph.has_base_search_state.to_base_state
    unfold WeightedDiGraph.instHas_base_search_stateBase_search_state
    apply le_trans
    · apply prop
    · clear prop t_1 t_2 t_3
      unfold final_state at p_path_length
      unfold final at p_path_length
      unfold WeightedDiGraph.search_with_stack_step at p_path_length
      simp_all
      rw [← p_path_length]
      unfold WeightedDiGraph.Path.is_cheapest at p_is_cheapest
      specialize p_is_cheapest p'
      simp_all


end NatGraph
