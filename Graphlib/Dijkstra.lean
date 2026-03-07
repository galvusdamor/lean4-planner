import Mathlib.Data.Bool.AllAny
import Mathlib.Data.FinEnum
import Mathlib.Data.Finset.Empty
import Mathlib.Data.List.MinMax
import Mathlib.Order.Basic
import Mathlib.Data.Multiset.DershowitzManna
import Mathlib.Data.Finsupp.WellFounded
import Mathlib.Data.List.ToFinsupp
import Mathlib.Data.List.Pairwise
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

@[simp]
abbrev search_invar_start_not_mem_tail (start : V) (s : WeightedDiGraph.base_search_state g (ℕ×ℕ)) :=
      start ∉ s.stack.tail


abbrev dijkstra_all_invar (start : V) (s : WeightedDiGraph.base_search_state g (ℕ×ℕ)) :=
      WeightedDiGraph.search_invar_all_basic start s
    ∧ dijkstra_stack_shortest_path start s
    ∧ dijkstra_path_order_diff_by_edge_cost start s
    ∧ dijkstra_invar_on_stack_or_all_neighbours_max_order s
    ∧ dijkstra_stack_sorted s
    ∧ search_invar_start_path_order_zero_zero start s
    ∧ search_invar_start_not_mem_tail start s



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
        · unfold search_invar_start_not_mem_tail
          unfold WeightedDiGraph.base_search_state_initial
          simp


section
variable (state : WeightedDiGraph.base_search_state g (ℕ×ℕ))


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


lemma dijkstra_expand_start_not_mem_tail_carries (start : V) (goal : V)
    (start_visited : WeightedDiGraph.search_invar_start_visited start state)
    (start_zero_zero : search_invar_start_path_order_zero_zero start state)
    :
     ∀ head : V, ∀ tail : List V, 
        search_invar_start_not_mem_tail start state
          ∧ ¬ head = goal
          ∧ state.stack = head :: tail
        → search_invar_start_not_mem_tail start (dijkstra_step_expand state head tail) := by
      intro head tail ⟨ prior_invar,head_ne_goal,compose⟩ 
      unfold search_invar_start_not_mem_tail
      unfold search_invar_start_path_order_zero_zero at start_zero_zero
      unfold dijkstra_step_expand
      simp_all
      intro start_in
      apply List.mem_of_mem_tail at start_in
      simp at start_in
      grind


lemma dijkstra_expand_keeps_shortest_path_invar_start
    (start : V) (goal : V)
    ----- co-invariants needed for path extraction
    --(mother_invar : WeightedDiGraph.search_invar_mother_is_visited state)
    --(mother_invar_adj : WeightedDiGraph.search_invar_mother_is_adjacent start state)
    --(decreasing_invar : WeightedDiGraph.search_invar_mother_decreasing_path_order start state)
    (start_visited : WeightedDiGraph.search_invar_start_visited start state)
    --(on_stack_or_nei_visited : WeightedDiGraph.search_invar_on_stack_or_all_neighbours_visited state)
    --(stack_visited_invar : WeightedDiGraph.search_invar_stack_is_visited state)
    -- new bfs_ specific invars
    --(path_order_diff : dijkstra_path_order_diff_by_edge_cost start state)
    --(extract_length_invar : dijkstra_path_as_extracted_as_long_as_sort_index start state)
    --(update_invar : dijkstra_invar_on_stack_or_all_neighbours_max_order state)
    --(stack_sorted : dijkstra_stack_sorted state)
    (start_path_order : search_invar_start_path_order_zero_zero start state)
    (head : V) (tail : List V)
    (head_is_not_goal : ¬head = goal)
    (compose : state.stack = head :: tail):
     g.cost_is start start ((dijkstra_step_expand state head tail).pathOrder start).1
     := by
      --simp at v_not_start
      --subst  [v_not_start] 
      unfold cost_is
      unfold search_invar_start_path_order_zero_zero at start_path_order
      have gg := start_path_order
      have still_zero : (dijkstra_step_expand state head tail).pathOrder start = 0 := by
        apply dijkstra_expand_start_path_order_zero_carries
        · apply start_visited
        · constructor
          · apply start_path_order
          · constructor
            · apply head_is_not_goal
            · apply compose

      rw [still_zero]
      use (g.nil_path start)
      unfold Path.is_cheapest
      constructor
      all_goals
        rw [Path.cost_nil_zero]
        simp

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
termination_by FValueComp.wf.wrap (s.pathOrder u)
decreasing_by
  apply decreasing_invar
  simp_all

 

--lemma dijkstra_new_head
--    (head : V) (tail : List V)
--    (head_is_not_goal : ¬head = goal)
--    (compose : state.stack = head :: tail)
--    (visited_before : v ∈ state.visited)
--    (stack_not_empty_after : ¬(dijkstra_step_expand state head tail).stack = [])
--    (head_after_is_v : (dijkstra_step_expand state head tail).stack.head stack_not_empty_after = v)
--    : ∃ tail_tail : List V, tail = v :: tail_tail := by
--     by_cases tail_ne_empty : tail ≠ []
--     · apply List.ne_nil_iff_exists_cons.mp at tail_ne_empty
--       obtain ⟨ b, tail_tail, cons ⟩ := tail_ne_empty
--       use tail_tail
--       rw [cons]
--       simp_all
--       
--     · simp at tail_ne_empty
--       subst tail_ne_empty
--       --unfold dijkstra_step_expand at head_after_is_v
--       --simp_all
--       
--       --apply Option.eq_some_if_get_eq at head_after_is_v
--       --apply List.findSome?_eq_some_iff.mp at head_after_is_v
--       --obtain ⟨l_1, a, l_2, ⟨ p,q,r⟩ ⟩ := head_after_is_v 
--       --simp_all
--       --obtain ⟨ ⟨ x1,x_2⟩ ,y⟩ := q 
--       --rw [y] at x_2
--       --contradiction
----have t_c : 




lemma dijkstra_new_head_cost_lt_other_on_stack_before
  (head : V) (tail : List V) (compose : state.stack = head :: tail)
  (u : V) (u_on_stack : u ∈ state.stack) (u_ne_head : u ≠ head)
  (u_visited : u ∈ state.visited)
  (v : V) (after_not_nil : (dijkstra_step_expand state head tail).stack ≠ [])
  (adj_head_v : g.Adj head v)
  (v_head_after : (dijkstra_step_expand state head tail).stack.head after_not_nil = v):
  ((dijkstra_step_expand state head tail).pathOrder v).1 ≤ (state.pathOrder u).1 := by
    unfold dijkstra_step_expand at v_head_after
    simp_all
    by_cases u_neq_v : u ≠ v
    · apply mergeSort_head_from_head_unsorted at v_head_after
      · specialize v_head_after u
        apply imp_iff_or_not.mp at v_head_after
        cases v_head_after
        case pos.inl p =>
          simp_all
          cases p
          case inl p =>
            split_ifs at p <;> (unfold dijkstra_step_expand ; simp_all ; try grind)
          case inr p =>
            split_ifs at p
            all_goals
              unfold FValueComp.lt_B at p
              unfold Nat.instFValueCompProd at p
              simp at p
              unfold dijkstra_step_expand
              simp_all
              grind
        case pos.inr p =>
          apply absurd p
          clear p
          simp
          intro u_not_in_tail
          contradiction
      · intro a b c ab bc
        apply dijkstra_merge_trans
        · apply ab
        · apply bc
      · intro a b
        apply dijkstra_merge_total
    · simp at u_neq_v
      subst u_neq_v
      clear v_head_after
      unfold dijkstra_step_expand
      simp_all
      split_ifs
      · rfl
      · rfl
      · grind

lemma dijkstra_new_head_cost_lt_other_on_stack_now
  (head : V) (tail : List V) 
  (u : V) (u_on_stack_after : u ∈ (dijkstra_step_expand state head tail).stack)
  (v : V) (after_not_nil : (dijkstra_step_expand state head tail).stack ≠ [])
  --(adj_head_v : g.Adj head v)
  (v_head_after : (dijkstra_step_expand state head tail).stack.head after_not_nil = v):
  ((dijkstra_step_expand state head tail).pathOrder v).1 ≤ ((dijkstra_step_expand state head tail).pathOrder u).1 := by
    unfold dijkstra_step_expand at v_head_after
    simp_all
    apply mergeSort_head_from_head_unsorted at v_head_after
    · specialize v_head_after u 
      apply imp_iff_or_not.mp at v_head_after
      cases v_head_after
      case inl p =>
        cases p
        case inl eq =>
          subst eq
          rfl
        case inr p =>
          simp_all
          split_ifs at p
          all_goals
            unfold dijkstra_step_expand
            unfold FValueComp.lt_B at p
            unfold Nat.instFValueCompProd at p
            simp_all
            grind
      case inr p =>
        unfold dijkstra_step_expand at u_on_stack_after
        simp_all
    · intro a b c ab bc
      apply dijkstra_merge_trans
      · apply ab
      · apply bc
    · intro a b
      apply dijkstra_merge_total



lemma split_1 (p : g.Path a b) (w : V) (w_in_supp : w ∈ p.val.support) (w_ne_a : w ≠ a): 
    ∃ u : V, ∃ au : g.Path a u, g.Adj u w := by
        -- Get a sub-path from a to w
  by_cases w_eq_b : w = b
  · -- w = b: use split_at_end on p itself
    subst w_eq_b
    obtain ⟨u, au, adj_u_w, _, _⟩ := p.split_at_end (Ne.symm w_ne_a)
    exact ⟨u, au, adj_u_w⟩
  · -- w ≠ b: use contains_subpath to get path a → w, then split_at_end
    obtain ⟨p_aw, _⟩ := WeightedDiGraph.Path.contains_subpath p w_in_supp w_eq_b
    obtain ⟨u, au, adj_u_w, _, _⟩ := p_aw.split_at_end (Ne.symm w_ne_a)
    exact ⟨u, au, adj_u_w⟩

omit [DecidableEq V] in 
private lemma track_walk_not_on_stack
  (on_stack_or_nei_visited : search_invar_on_stack_or_all_neighbours_visited state)
  (start_visited : search_invar_start_visited start state)
  (w_w : g.Walk start w)
  (w_nodup : w_w.support.Nodup)
  (no_pw_mem_on_stack : ∀ x ∈ w_w.support, x ∉ state.stack):
    ∀ x ∈ w_w.support, x ∈ state.visited := by
      cases w_w
      case nil =>
        intro x x_in_nil_supp
        simp_all
      case cons w' h p =>
        intro x x_in_supp
        unfold  Walk.support at x_in_supp
        apply List.mem_cons.mp at x_in_supp
        cases x_in_supp
        case inl x_is_start =>
          grind
        case inr x_in_p_support =>
          have p_nodup : p.support.Nodup := by
            unfold Walk.support at w_nodup
            apply List.nodup_cons.mp at w_nodup
            exact w_nodup.2
          apply track_walk_not_on_stack (w_w := p)
          · exact on_stack_or_nei_visited
          · unfold search_invar_start_visited at ⊢ start_visited
            unfold search_invar_on_stack_or_all_neighbours_visited at on_stack_or_nei_visited
            have start_not_on_stack : start ∉ state.stack := by
              apply no_pw_mem_on_stack
              unfold Walk.support
              simp
            specialize on_stack_or_nei_visited ⟨start, start_visited ⟩ 
            simp_all
          · exact p_nodup
          · intro y y_in_pp_supp
            apply no_pw_mem_on_stack
            unfold Walk.support
            apply List.mem_cons.mpr
            right
            apply y_in_pp_supp
          · apply x_in_p_support

omit [DecidableEq V] in
private lemma track_path_not_on_stack
  (on_stack_or_nei_visited : search_invar_on_stack_or_all_neighbours_visited state)
  (start_visited : search_invar_start_visited start state)
  (p_w : g.Path start w)
  (no_pw_mem_on_stack : ∀ x ∈ p_w.support, x ∉ state.stack):
    ∀ x ∈ p_w.support, x ∈ state.visited := by
      intro x x_in_supp
      apply track_walk_not_on_stack (w_w := p_w.val)
      · apply on_stack_or_nei_visited
      · apply start_visited
      · exact p_w.prop
      · intro y y_in_pw_supp
        apply no_pw_mem_on_stack
        apply y_in_pw_supp
      · apply x_in_supp


--have v_after_eq_e_sh: ((dijkstra_step_expand state head tail).pathOrder v).1 = e + path_to_head.cost := by
--(mother_and_edge_smaller_order_before : (state.pathOrder the_mother).1 + edgeCost adj_mother_v ≤ (state.pathOrder v).1)
--path_mother.cost + e ≤ ((dijkstra_step_expand state head tail).pathOrder v).1

/--
  The node v is the head of the stack after this expansion.
  I.e. it is smaller than all other nodes on the stack, after the expansion.
  v has a mother (the_mother). There is a path from start to the_mother, that is a shortest path.
  the_mother is visited, but is not on the stack or was the head.
  Notably, this implies that the pathOrder of the_mother is the cost of that path.


  In addition, we have a path p' that is supposedly shorter than the path start->the_mother->v
  Now, p' contains a first node u that is still on the stack (this lemma only treats this case, if not use other lemma)
  We can now consider the sub-path of p' from start to u

-/
private lemma dijkstra_shorter_path_first_on_stack_not_head {start : V}
(the_mother : V)
(v : V)
(u : V)
--(mother_invar : search_invar_mother_is_visited state)
--(mother_invar_adj : search_invar_mother_is_adjacent start state)
--(decreasing_invar : search_invar_mother_decreasing_path_order start state)
(start_visited : search_invar_start_visited start state)
(on_stack_or_nei_visited : search_invar_on_stack_or_all_neighbours_visited state)
--(stack_visited_invar : search_invar_stack_is_visited state)
--(path_order_diff : dijkstra_path_order_diff_by_edge_cost start state)
(update_invar : dijkstra_invar_on_stack_or_all_neighbours_max_order state)
--(stack_sorted : dijkstra_stack_sorted state)
--(start_path_order : search_invar_start_path_order_zero_zero start state)
(start_not_mem_tail : search_invar_start_not_mem_tail start state)
(head : V)
(tail : List V)
(prior_invar : dijkstra_stack_shortest_path start state)
(compose : state.stack = head :: tail)
--  (v_visited_after : v ∈ (dijkstra_step_expand state head tail).visited)
  --(head_was_visited_before : head ∈ state.visited)
  --(path_to_head : g.Path start head)
  --(ph_eq_dh : path_to_head.cost = (state.pathOrder head).1)
  --(support_visited : ∀ u ∈ path_to_head.val.support, u ∈ state.visited)
  --(v_not_start : v ≠ start)
--  (stack_not_empty_after : ¬(dijkstra_step_expand state head tail).stack = [])
  --(head_after_is_v : (dijkstra_step_expand state head tail).stack.head stack_not_empty_after = v)
--(v_visited : v ∈ state.visited)
--(mother_visited : the_mother ∈ state.visited)
--(mother_not_on_stack_or_head : the_mother ∉ state.stack ∨ the_mother = head)
--  (the_mother_is : the_mother = state.mother ⟨v, v_visited⟩)
--  (mother_same : (dijkstra_step_expand state head tail).mother ⟨v, v_visited_after⟩ = the_mother)
--  (mother_ne_head : the_mother ≠ head)
--  (pathOrder_unchanged : (dijkstra_step_expand state head tail).pathOrder v = state.pathOrder v)
(adj_mother_v : g.Adj the_mother v)
--  (mother_and_edge_smaller_order_before : (state.pathOrder the_mother).1 + edgeCost adj_mother_v ≤ (state.pathOrder v).1)
--  (pathOrder_mother_decreases : ((dijkstra_step_expand state head tail).pathOrder the_mother).1 ≤ (state.pathOrder the_mother).1)

--- there is a path from start to the_mother
(path_mother : Path start the_mother)
--(path_mother_is : path_mother = (extract_path_to start the_mother state mother_visited mother_invar mother_invar_adj decreasing_invar).fst)
----
(v_not_in_mother_path : v ∉ path_mother.val.support)
(path_mother_v : Path start v)
(path_mother_v_is : path_mother_v = path_mother.concat adj_mother_v v_not_in_mother_path)
------ p' is the supposedly shorter path
(p' : g.Path start v)
(p'_cheaper : p'.val.cost < path_mother_v.val.cost)
--
(u_in_support : u ∈ p'.val.support)
(u_on_stack : u ∈ state.stack)
(u_ne_v : u ≠ v)
(prior_not_on_stack : ((List.takeWhile (fun x => decide (x ≠ u)) p'.support).all fun x => decide (x ∉ state.stack)) = true)
(u_visited : u ∈ state.visited)
(su : g.Path start u)
(cheaper : su.cost ≤ p'.cost)
(u_ne_head : head ≠ u)
(mother_plus_e_le_u : path_mother.cost + g.edgeCost adj_mother_v ≤ (state.pathOrder u).1 )
:
⊥ := by
  let e := g.edgeCost adj_mother_v
  obtain ⟨su, cheaper, supp_subseq⟩ := p'.contains_subpath_cost u_in_support u_ne_v
  
  -- u cannot be the start node (as u has to be on the stack and cannot be head)
  have u_ne_start : start ≠ u := by
    by_contra
    subst this
    --simp_all
    simp [*] at u_on_stack
    cases u_on_stack
    · grind
    · next start_in_tail =>
      unfold search_invar_start_not_mem_tail at start_not_mem_tail 
      grind
  
  -- this allows us to consider the predecessor of u on the path su - which we call w
  obtain ⟨ w,p_w,adj_w_u,u_not_earlier_in_path,su_compose⟩ := su.split_at_end u_ne_start
 
  have no_pw_mem_on_stack : ∀ x ∈ p_w.support, x ∉ state.stack := by
    intro x x_in_support
    unfold Path.support at prior_not_on_stack supp_subseq
    rw [su_compose] at supp_subseq
    simp at supp_subseq
    unfold List.IsPrefix at supp_subseq
    obtain ⟨ t, compose ⟩ := supp_subseq
    rw [← compose] at prior_not_on_stack
    rw [List.append_assoc] at prior_not_on_stack
    rw [List.takeWhile_append_of_pos] at prior_not_on_stack
    · rw [List.all_append] at prior_not_on_stack
      apply Bool.and_elim_left at prior_not_on_stack
      apply List.all_iff_forall_prop.mp at prior_not_on_stack
      apply prior_not_on_stack
      apply x_in_support
    · grind
  
  -- w now has to not be part of the stack (as u was the first node to be on the stack!)
  have w_not_on_stack : w ∉ state.stack := by
    apply no_pw_mem_on_stack
    apply Walk.goal_in_support

  have w_visited : w ∈ state.visited := by
    apply track_path_not_on_stack (p_w := p_w)
    · exact on_stack_or_nei_visited
    · exact start_visited
    · exact no_pw_mem_on_stack
    · apply Path.goal_in_support
  
  let f := edgeCost adj_w_u 
  have p_w_le_su : p_w.cost + f = su.cost := by
    conv => right ; unfold Path.cost
    rw [su_compose]
    unfold f
    rw [add_comm]
    rw [Walk.concat_inc_cost_by_edge]
    rfl
  -- Eq 8
  have du_le_sq_f : (state.pathOrder u).1 ≤ p_w.cost + f := by
    unfold dijkstra_stack_shortest_path at prior_invar
    specialize prior_invar w w_visited
    --simp_all
    unfold cost_is at prior_invar
    rw [or_imp] at prior_invar
    obtain ⟨prior_invar, _ ⟩ := prior_invar
    specialize prior_invar w_not_on_stack
    obtain ⟨ sp, cost_is_order,is_cheapest ⟩ := prior_invar
    unfold Path.is_cheapest at is_cheapest
    specialize is_cheapest p_w
    conv at is_cheapest => right ; unfold Path.cost
    have w_sp : (state.pathOrder w).1 ≤ p_w.val.cost := by omega
    apply le_trans
    rotate_left
    · apply add_le_add_left
      apply w_sp
    · unfold dijkstra_invar_on_stack_or_all_neighbours_max_order at update_invar 
      specialize update_invar ⟨ w, w_visited ⟩ w_not_on_stack u adj_w_u
      omega

  --have dh_le_sw_f : (state.pathOrder head).1 ≤ p_w.cost + f := by omega
  
  -- Eq 9: from head already optimal
  --have ph_le_sw_f : path_to_head.cost ≤ p_w.cost + f := by omega
  --have ph_e_le_sw_f_e : path_to_head.cost + e ≤ p_w.cost + f + e := by omega
  --have su_lt_sw_f_e : su.cost < p_w.cost + f + e := by omega
  
  --have xxx : (state.pathOrder the_mother).1 = path_mother.cost := by sorry
  --have xxxx : (state.pathOrder the_mother).1 + e = path_mother_v.cost := by sorry

  have p'_lt_mp_plus_e : p'.cost < path_mother.cost + e := by
    unfold Path.cost
    convert p'_cheaper
    rw [path_mother_v_is]
    unfold Path.concat
    simp [Walk.concat_inc_cost_by_edge]
    grind

  --have updated_value_at_most :  ≤ ((dijkstra_step_expand state head tail).pathOrder v).1 := by
  --  -- due to update on mother
  --  unfold dijkstra_path_order_diff_by_edge_cost at path_order_diff
  --  specialize path_order_diff mother_invar_adj v v_visited v_not_start
  --  sorry
  --  --unfold the_mother
  --  --grind
  --   --unfold dijkstra_invar_on_stack_or_all_neighbours_max_order at update_invar
  --  --cases mother_not_on_stack_or_head
  --  --case inl mother_not_on_stack =>
  --  --  specialize update_invar ⟨ the_mother, mother_visited ⟩ mother_not_on_stack v adj_mother_v
  --  --  sorry
  --  --· sorry
  --
  --have updated_value_le_other : ((dijkstra_step_expand state head tail).pathOrder v).1 ≤ ((dijkstra_step_expand state head tail).pathOrder u).1 := by
  --  -- due to v being head of stack after
  --  sorry
  --
  --have later_value_le : ((dijkstra_step_expand state head tail).pathOrder u).1 ≤ (state.pathOrder u).1 := by
  --  unfold dijkstra_step_expand
  --  simp
  --  grind

  have p'_lt_du : p'.cost < (state.pathOrder u).1 := by omega
  have p'_lt_sw_f : p'.cost < p_w.cost + f := by omega

  omega 



lemma dijkstra_path_head_adj_new_head_is_cheapest {start : V}
    (start_visited : start ∈ state.visited)
    (stack_visited_invar : WeightedDiGraph.search_invar_stack_is_visited state)
    (on_stack_or_nei_visited : search_invar_on_stack_or_all_neighbours_visited state)
    (update_invar : dijkstra_invar_on_stack_or_all_neighbours_max_order state)
    (start_path_order : search_invar_start_path_order_zero_zero start state)
    (prior_invar : dijkstra_stack_shortest_path start state)
    (start_not_mem_tail : search_invar_start_not_mem_tail start state)
    -- execution of current step
    {head : V} {tail : List V}
    (compose : state.stack = head :: tail)
    (head_was_visited_before : head ∈ state.visited)
    (path_to_head : g.Path start head)
    (ph_eq_dh : path_to_head.cost = (state.pathOrder head).1)
    -- the new head of the stack -- 
    (v : V)
    (v_not_start : v ≠ start)
    (stack_not_empty_after : ¬(dijkstra_step_expand state head tail).stack = [])
    (head_after_is_v : (dijkstra_step_expand state head tail).stack.head stack_not_empty_after = v)
    (adj_head_v : g.Adj head v)
    (v_order_eq_head_plus_edge : ((dijkstra_step_expand state head tail).pathOrder v).1 = ((dijkstra_step_expand state head tail).pathOrder head).1 + g.edgeCost adj_head_v)
    (support_visited : ∀ u ∈ path_to_head.val.support, u ∈ state.visited)
    (v_not_in_support_ph : v ∉ path_to_head.val.support)
    (path_explored_contra : ∀ p : g.Path start v, (p.cost < (path_to_head.concat adj_head_v v_not_in_support_ph).cost ∧ v ∈ state.visited ∧ ∀ u ∈ p.support, u ≠ v → u ∉ state.stack ∧ u ∈ state.visited) → ⊥)
    (path_explored_contra_head : ∀ w : V, w ≠ head → ∀ adj_h_w : g.Adj head w, ∀ p : g.Path w v, (p.cost + g.edgeCost adj_h_w < g.edgeCost adj_head_v ∧ v ∈ state.visited ∧ ∀ u ∈ p.support, u ≠ v → u ∉ state.stack ∧ u ∈ state.visited) → ⊥)
    :
    (path_to_head.concat adj_head_v v_not_in_support_ph).is_cheapest := by
      let path_to_v := path_to_head.concat adj_head_v v_not_in_support_ph
      let e := g.edgeCost adj_head_v

      -- Situation: v is head of stack after expansion of head
      -- v was added to the stack due to expansion of v (i.e. it was not visited before)
      -- ph (path_to_head) is a shortest path to head
      -- selected apth to v is (path_to_head ; <head,v>)
      -- 
      -- Now: Assume there is a shorter path to v: p'
      unfold Path.is_cheapest
      intro p'
      by_contra p'_is_cheaper
      simp at p'_is_cheaper


      -- we can run along p' until we find a first node in p' that is still on the stack (before the expansion)
      -- or (second case) no node is on the stack, but then all nodes are visited
      have p'_elem_on_stack_or_v_visited :
        -- possibly stronger: the all elements are also visited!
        (∃ u ∈ p'.val.support, u ∈ state.stack ∧ u ≠ v ∧ (p'.support.takeWhile (· ≠ u)).all (· ∉ state.stack)) ∨
          (v ∈ state.visited ∧ ∀ u ∈ p'.val.support, u ≠ v → u ∉ state.stack ∧ u ∈ state.visited) := 
        run_path_through_state_yields_node_on_stack_or_all_visited start v v_not_start p' state start_visited on_stack_or_nei_visited
      -- p' must be cheaper than the cost of path_to_v -- which is path_to_head.cost + e (by construction)
      -- Eq 1: by expand p'_is_cheaper
      have su_lt_sh_e : p'.cost < path_to_head.cost + e := by
        unfold Path.cost
        convert p'_is_cheaper
        unfold Path.concat
        simp_all only [Walk.start_in_support, search_invar_stack_is_visited, List.mem_cons, forall_eq_or_imp, true_and,search_invar_on_stack_or_all_neighbours_visited, Subtype.forall, not_or, and_imp, Walk.goal_in_support,Path.cost_same, ne_eq, Path.support, «Prop».bot_eq_false, imp_false, not_and, not_forall, decide_not, Bool.decide_and, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,decide_eq_false_iff_not, Walk.concat_inc_cost_by_edge]
        rw [add_comm]
      -- we set the pathCost of v to exactly this value
      have v_after_eq_e_sh: ((dijkstra_step_expand state head tail).pathOrder v).1 = e + path_to_head.cost := by
        unfold dijkstra_step_expand
        unfold e
        --simp_all
        rw [add_comm]
        simp
        split_ifs
        · rename_i _ v_visited lt
          unfold dijkstra_step_expand at v_order_eq_head_plus_edge
          simp_all
          grind
        · simp_all
        · simp_all
        · simp_all
        · simp_all

      cases p'_elem_on_stack_or_v_visited
      · next u_in_support_on_stack =>
        -- first node in p that is on the stack: call it u
        -- all nodes before u are not on the stack, i.e. paths to them are shortest paths.
        obtain ⟨u, ⟨u_in_support, ⟨ u_on_stack, u_ne_v, prior_not_on_stack⟩ ⟩ ⟩ := u_in_support_on_stack
        have u_visited : u ∈ state.visited := by grind 
        -- extract path from start to this node u
        -- su is not longer than p' itself
        -- cheaper is Eq 5. (su) ≤ p'
        obtain ⟨ su, cheaper⟩ := p'.contains_subpath_cost u_in_support u_ne_v

        -- Now 
 
        by_cases u_ne_head : head ≠ u
        · -- Eq 2: v is now the stack head
          have e_sh_le_du : e + path_to_head.cost ≤ (state.pathOrder u).1 := by
            rw [← v_after_eq_e_sh]
            apply dijkstra_new_head_cost_lt_other_on_stack_before
            · exact compose
            · exact u_on_stack
            · exact u_ne_head.symm
            · grind
            · exact adj_head_v 
            · apply head_after_is_v
          -- Eq 6: d(h) ≤ d(u) (from h being the stack head)
          --have dh_le_du : (state.pathOrder head).1 ≤ (state.pathOrder u).1 := by 

          --have su_lt_sh_e : su.cost < path_to_head.cost + e := by omega
          apply dijkstra_shorter_path_first_on_stack_not_head (the_mother:=head) (v:=v) (u:=u) (start:=start) <;> try assumption
          · rfl
          · exact cheaper.1
          · grind

          --have u_ne_start : start ≠ u := by
          --  by_contra
          --  subst this
          --  simp_all?
          --

          --obtain ⟨ w,p_w,adj_w_u,u_not_earlier_in_path,su_compose⟩ := su.split_at_end u_ne_start

          ----obtain ⟨w,p_w,adj_w_u⟩ := split_1 p' u u_in_support (Ne.symm u_ne_start)
          ----obtain ⟨w,p_w,adj_w_u⟩ := split_1 p' u u_in_support (Ne.symm u_ne_start)

          ---- w is the predecessor of u on p'
          ----have w : V := by 
          ----have p_w : g.Path start w := by 
          ----have adj_w_u : g.Adj w u := by 
          --have w_not_on_stack : w ∉ state.stack := by sorry
          --have w_visited : w ∈ state.visited := by sorry
          --let f := edgeCost adj_w_u 
          --have p_w_le_su : p_w.cost + f = su.cost := by
          --  conv => right ; unfold Path.cost
          --  rw [su_compose]
          --  unfold f
          --  rw [add_comm]
          --  rw [Walk.concat_inc_cost_by_edge]
          --  rfl
          ---- Eq 8
          --have du_le_sq_f : (state.pathOrder u).1 ≤ p_w.cost + f := by
          --  unfold dijkstra_stack_shortest_path at prior_invar
          --  specialize prior_invar w w_visited
          --  simp_all
          --  unfold cost_is at prior_invar
          --  obtain ⟨ sp, cost_is_order,is_cheapest ⟩ := prior_invar
          --  unfold Path.is_cheapest at is_cheapest
          --  specialize is_cheapest p_w
          --  conv at is_cheapest => right ; unfold Path.cost
          --  have w_sp : (state.pathOrder w).1 ≤ p_w.val.cost := by omega
          --  apply le_trans
          --  rotate_left
          --  · apply add_le_add_right
          --    apply w_sp
          --  · specialize update_invar w w_visited w_not_on_stack.left w_not_on_stack.right u adj_w_u
          --    omega

          ----have dh_le_sw_f : (state.pathOrder head).1 ≤ p_w.cost + f := by omega
          --
          ---- Eq 9: from head already optimal
          ----have ph_le_sw_f : path_to_head.cost ≤ p_w.cost + f := by omega
          ----have ph_e_le_sw_f_e : path_to_head.cost + e ≤ p_w.cost + f + e := by omega
          ----have su_lt_sw_f_e : su.cost < p_w.cost + f + e := by omega
          --
          --have p'_lt_du : p'.cost < (state.pathOrder u).1 := by omega
          --have p'_lt_sw_f : p'.cost < p_w.cost + f := by omega

          --omega 
        · simp at u_ne_head

          have su_ge_ph : su.cost ≥ path_to_head.cost := by
            subst u_ne_head
            unfold dijkstra_stack_shortest_path at prior_invar
            specialize prior_invar head head_was_visited_before
            --simp_all?
            unfold cost_is at prior_invar
            simp [u_on_stack] at prior_invar
            have stack_ne_nil : state.stack ≠ [] := by grind
            specialize prior_invar stack_ne_nil
            simp [compose] at prior_invar
            obtain ⟨hp, ⟨ hp_cost, ⟨ nodup , hp_cheapest ⟩ ⟩ ⟩ := prior_invar
            unfold Path.is_cheapest at hp_cheapest
            specialize hp_cheapest su
            simp_all only [Walk.start_in_support, search_invar_stack_is_visited, List.mem_cons, forall_eq_or_imp, true_and,search_invar_on_stack_or_all_neighbours_visited, Subtype.forall, not_or, and_imp, Walk.goal_in_support,Path.cost_same, ne_eq, Path.support, «Prop».bot_eq_false, imp_false, not_and, not_forall, true_or, decide_not, Bool.decide_and, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,decide_eq_false_iff_not, reduceCtorEq, not_false_eq_true, ge_iff_le]


          -- split p' at u
          -- remainder of the p' path
          have path_uv : g.Path u v := by sorry
          have p'_cost : p'.cost = su.cost + path_uv.cost := by sorry
         
          have uv_lt_e : path_uv.cost < e := by omega

          have v_ne_head : v ≠ head := by grind
          subst u_ne_head

          cases comp : path_uv.val
          · grind
          case neg.cons w h p =>
            let f := edgeCost h
            have uv_eq_f_plus_p : path_uv.cost = f + p.cost := by
              unfold Path.cost
              rw [comp]
              conv => left ; unfold Walk.cost
            unfold Path.cost at uv_lt_e
            rw [comp] at uv_lt_e
            unfold Walk.cost at uv_lt_e
            by_cases w_ne_v : w ≠ v
            · have w_ne_head : w ≠ head := by
                by_contra w_eq_head
                subst w_eq_head 
                have pp := path_uv.prop
                rw [comp] at pp
                unfold Walk.support at pp
                unfold List.Nodup at pp
                apply List.pairwise_cons.mp at pp
                rcases pp with ⟨all_diff,_⟩ 
                specialize all_diff w
                have w_in_p_supp : w ∈ p.support := by simp
                simp_all only [Walk.start_in_support, search_invar_stack_is_visited, List.mem_cons, forall_eq_or_imp, true_and,search_invar_on_stack_or_all_neighbours_visited, Subtype.forall, not_or, and_imp, ne_eq, not_false_eq_true,Walk.goal_in_support, Path.cost_same, Path.support, «Prop».bot_eq_false, imp_false, not_and, not_forall, true_or, decide_not, Bool.decide_and, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_eq_eq_not,Bool.not_true, decide_eq_false_iff_not, ge_iff_le, not_true_eq_false]
              have w_visited_after : w ∈ (dijkstra_step_expand state head tail).visited := by
                unfold dijkstra_step_expand ; grind
              by_cases w_visited_before : w ∈ state.visited
              · clear su cheaper su_ge_ph p'_cost
                have p_nondup : List.Nodup p.support := by
                  have nondup := path_uv.prop
                  rw [comp] at nondup
                  rw [Walk.support_cons] at nondup
                  exact List.Nodup.of_cons nondup
                let p_path : Path w v := ⟨p,p_nondup⟩ 

                have p_elem_on_stack_or_v_visited :
                  (∃ u ∈ p_path.val.support, u ∈ state.stack ∧ u ≠ v ∧ (p_path.support.takeWhile (· ≠ u)).all (· ∉ state.stack)) ∨
                    (v ∈ state.visited ∧ ∀ u ∈ p_path.val.support, u ≠ v → u ∉ state.stack ∧ u ∈ state.visited) := 
                  run_path_through_state_yields_node_on_stack_or_all_visited w v w_ne_v.symm p_path state w_visited_before on_stack_or_nei_visited

                
                cases p_elem_on_stack_or_v_visited
                · rename_i ex
                  obtain ⟨q,⟨q_in_supp, ⟨q_on_stack, ⟨q_ne_v, _⟩ ⟩⟩⟩ := ex
                  have q_ne_head : q ≠ head := by
                    by_contra q_eq_head
                    subst q_eq_head 
                    have pp := path_uv.prop
                    rw [comp] at pp
                    unfold Walk.support at pp
                    unfold List.Nodup at pp
                    apply List.pairwise_cons.mp at pp
                    rcases pp with ⟨all_diff,_⟩ 
                    specialize all_diff q
                    have q_in_p_supp : q ∈ p.support := by
                      unfold p_path at q_in_supp
                      simp at q_in_supp
                      exact q_in_supp
                    simp_all
                  

                  have q_on_stack_after : q ∈ (dijkstra_step_expand state head tail).stack := by
                    unfold dijkstra_step_expand ; simp ; grind
                  have q_order_ge_v_order_after : ((dijkstra_step_expand state head tail).pathOrder q).1 ≥ ((dijkstra_step_expand state head tail).pathOrder v).1 := by
                    apply dijkstra_new_head_cost_lt_other_on_stack_now
                    · exact q_on_stack_after
                    · apply head_after_is_v

                  obtain ⟨ wq, cheaper⟩ := p_path.contains_subpath_cost q_in_supp q_ne_v

                  have f_wq_lt_e : f + wq.cost < e := by
                    obtain ⟨ cheaper , _ ⟩ := cheaper
                    conv at cheaper =>
                      right
                      unfold p_path Path.cost
                      simp 
                    omega
                  

                  have e_sh_le_du : e + path_to_head.cost ≤ (state.pathOrder q).1 := by
                    rw [← v_after_eq_e_sh]
                    apply dijkstra_new_head_cost_lt_other_on_stack_before
                    · exact compose
                    · exact q_on_stack
                    · exact q_ne_head
                    · grind
                    · exact adj_head_v 
                    · apply head_after_is_v
                  
       
                  -- q' is the predecessor of q on p
                  have q' : V := by sorry
                  have p_q' : g.Path w q' := by sorry
                  have q'_not_on_stack : q' ∉ state.stack := by sorry
                  have q'_visited : q' ∈ state.visited := by sorry
                  have adj_q'_q : g.Adj q' q := by sorry
                  let f' := edgeCost adj_q'_q 
                  have p_q'_le_wq : p_q'.cost + f' = wq.cost := by sorry
                  -- from q' not on stack and thus optimal
                  let path_head_f : g.Path start w := path_to_head.concat h (by sorry)
                  let path_head_f_q' : g.Path start q' := path_head_f.append p_q' (by sorry)
                  
                  have dq'_le : (state.pathOrder q').1 ≤ path_to_head.cost + f + p_q'.cost := by
                    unfold dijkstra_stack_shortest_path at prior_invar
                    specialize prior_invar q' q'_visited
                    simp_all
                    unfold cost_is at prior_invar
                    obtain ⟨sp,⟨is,shortest_path⟩⟩ := prior_invar
                    unfold Path.is_cheapest at shortest_path
                    -- use List.Nodup.sublist for proof
                    specialize shortest_path path_head_f_q'
                    rw [← is]
                    have new_path_cost : path_head_f_q'.cost = path_to_head.cost + f + p_q'.cost := by
                      have h1 : path_head_f_q'.val.cost = path_head_f.val.cost + p_q'.val.cost := by
                        unfold path_head_f_q' Path.append
                        simp [Walk.append_cost]
                      have h2 : path_head_f.val.cost = path_to_head.val.cost + f := by
                        unfold path_head_f Path.concat
                        simp [Walk.concat_inc_cost_by_edge, f, edgeCost, add_comm]
                      unfold Path.cost at *
                      omega
                    rw [new_path_cost] at shortest_path
                    rw [←ph_eq_dh]
                    apply shortest_path

                  -- from neighbour update
                  have dq_le_sq_f : (state.pathOrder q).1 ≤ path_to_head.cost + f + p_q'.cost + f' := by
                    unfold dijkstra_invar_on_stack_or_all_neighbours_max_order at update_invar
                    specialize update_invar ⟨q', q'_visited⟩
                    simp_all
                    specialize update_invar q adj_q'_q
                    omega
                  omega 
                · --grind -- contradictory, as v would have been visited before
                  specialize path_explored_contra_head w w_ne_head h p_path 
                  simp_all
                  unfold p_path at path_explored_contra_head
                  simp at path_explored_contra_head
                  omega

              · have w_on_stack_after : w ∈ (dijkstra_step_expand state head tail).stack := by
                  unfold dijkstra_step_expand ; simp ; grind
                have w_order_ge_v_order_after : ((dijkstra_step_expand state head tail).pathOrder w).1 ≥ ((dijkstra_step_expand state head tail).pathOrder v).1 := by
                  apply dijkstra_new_head_cost_lt_other_on_stack_now
                  · exact w_on_stack_after
                  · apply head_after_is_v
                have f_ge_e : f ≥ e := by
                  unfold dijkstra_step_expand at w_order_ge_v_order_after
                  simp_all
                  by_cases v_visited : v ∈ state.visited
                  · split at w_order_ge_v_order_after
                    · split at w_order_ge_v_order_after
                      · rename_i v_lt_head_edge
                        unfold edgeCost at v_lt_head_edge
                        unfold e f edgeCost
                        unfold edgeCost at w_order_ge_v_order_after
                        unfold dijkstra_step_expand at v_after_eq_e_sh
                        unfold dijkstra_step_expand at v_order_eq_head_plus_edge
                        simp_all
                        split_ifs at v_after_eq_e_sh <;> try omega
                        · simp_all
                          unfold edgeCost at w_order_ge_v_order_after
                          apply w_order_ge_v_order_after
                        · simp_all
                          unfold edgeCost at w_order_ge_v_order_after
                          apply w_order_ge_v_order_after
                        · simp_all
                          unfold edgeCost at w_order_ge_v_order_after
                          apply w_order_ge_v_order_after
                        · rename_i a b c d 
                          simp_all
                          unfold edgeCost at a
                          omega
                        · rename_i a b c d e 
                          simp_all
                          unfold edgeCost at a
                          omega
                        · rename_i a b c 
                          simp_all
                          unfold edgeCost at a
                          omega
                      · split at w_order_ge_v_order_after <;> grind
                    · contradiction
                  · simp_all
                    exact w_order_ge_v_order_after
                omega
            · -- w is equal to v (contradiction, e + x < e)
              grind

      · next h =>
        have v_visited := h.left
        specialize path_explored_contra p'
        simp_all



/-- given an s v path and a node u on that path and the fact that u is not v, we can split the path into three parts:
    1) the path from s to u, the edge u u', and a path from u' to v-/
lemma Path.recompose {s v u: V} (p : g.Path s v) (u_on_p : u ∈ p.support):
    ∃ u' : V, ∃ s_u : g.Path s u, ∃ adj_u_u' : g.Adj u u', ∃ u'_v : g.Path u' v,
      ∃ u'_supp : u' ∉ s_u.val.support,
      ∃ u'_v_path_supp : (∀ a ∈ (s_u.concat adj_u_u' u'_supp).val.support, ∀ b ∈ u'_v.val.support.tail, a ≠ b),
      p = (s_u.concat adj_u_u' u'_supp).append u'_v u'_v_path_supp := by sorry


private lemma dijkstra_shorter_path_with_optimal_node_and_adj_on_stack
  {s v : V}
  (p : g.Path s v)
  (head : V)
  (tail : List V)
  (compose : state.stack = head :: tail)
  (update_invar : dijkstra_invar_on_stack_or_all_neighbours_max_order state)
  (p_path_cost : p.val.cost ≤ ((dijkstra_step_expand state head tail).pathOrder v).1)
  (stack_not_empty_after : ¬(dijkstra_step_expand state head tail).stack = [])
  (head_after_is_v : (dijkstra_step_expand state head tail).stack.head stack_not_empty_after = v)
  -- p' is a shorter path
  (p' : g.Path s v) 
  (p'_cheaper : p'.val.cost < p.val.cost)
  -- two nodes on p'
  (u u' : V)
  (u_visited : u ∈ state.visited)
  (u_not_in_stack_tail: u ∉ state.stack.tail)
  (u'_visited : u' ∈ state.visited)
  (u'_on_stack : u' ∈ state.stack)
  (u'_ne_head : u' ≠ head)
  (adj_u_u' : g.Adj u u')
  (p'_u : g.Walk s u)
  (p'_u_edge_le_p' : (p'_u.concat adj_u_u').cost ≤ p'.val.cost)
  --(p'_contains : ⊤)
  (u_cost_is : g.cost_is s u (state.pathOrder u).1)
: ⊥ := by

  -- w is on stack and must thus be larger
  have h4 : ((dijkstra_step_expand state head tail).pathOrder v).1 ≤  ((dijkstra_step_expand state head tail).pathOrder u').1:= by 
    apply dijkstra_new_head_cost_lt_other_on_stack_now
    · unfold dijkstra_step_expand ; simp ; grind
    · apply head_after_is_v

  -- state order of w can only have decreased by expansion (as it was visited before)
  have h5: ((dijkstra_step_expand state head tail).pathOrder u').1 ≤ (state.pathOrder u').1 := by
    unfold dijkstra_step_expand ; simp ; grind

  have h6 : ((dijkstra_step_expand state head tail).pathOrder u').1 ≤ p'.val.cost := by
    apply le_trans ; rotate_left
    · apply p'_u_edge_le_p'
    · unfold cost_is at u_cost_is
      obtain ⟨shortest, shortest_eq_pathOrder, is_cheapest ⟩ := u_cost_is
      unfold Path.is_cheapest at is_cheapest
      rw [shortest_eq_pathOrder] at is_cheapest
      clear shortest shortest_eq_pathOrder
      --have w_sp : (state.pathOrder w).1 ≤ p_w.val.cost := by omega
      apply le_trans
      rotate_left
      · simp
        apply add_le_add_right
        
        obtain ⟨cp, sp_cheaper ⟩ := p'_u.cheaper_path_exists
        apply le_trans --; rotate_left
        · apply is_cheapest cp
        · apply sp_cheaper
      · unfold dijkstra_invar_on_stack_or_all_neighbours_max_order at update_invar
        by_cases u_eq_head : u = head
        · unfold dijkstra_step_expand
          simp
          grind
        · apply le_trans
          · apply h5
          · specialize update_invar ⟨ u, u_visited ⟩ (by grind) u' adj_u_u'
            simp only at update_invar
            rw [add_comm]
            exact update_invar
        
  ---- path order of w was updated when expanding its predecessors, who is 
  omega




lemma dijkstra_path_mother_adj_new_head_is_cheapest {start : V}
    (mother_invar : search_invar_mother_is_visited state)
    (mother_invar_adj : search_invar_mother_is_adjacent start state)
    (decreasing_invar : search_invar_mother_decreasing_path_order start state)
    (start_visited : search_invar_start_visited start state)
    (on_stack_or_nei_visited : search_invar_on_stack_or_all_neighbours_visited state)
    (stack_visited_invar : search_invar_stack_is_visited state)
    (path_order_diff : dijkstra_path_order_diff_by_edge_cost start state)
    (update_invar : dijkstra_invar_on_stack_or_all_neighbours_max_order state)
    (stack_sorted : dijkstra_stack_sorted state)
    (start_path_order : search_invar_start_path_order_zero_zero start state)
    (start_not_mem_tail : search_invar_start_not_mem_tail start state)
    (head : V)
    (tail : List V)
    (prior_invar : dijkstra_stack_shortest_path start state)
    (compose : state.stack = head :: tail)
    (v : V)
    (v_visited_after : v ∈ (dijkstra_step_expand state head tail).visited)
    (head_was_visited_before : head ∈ state.visited)
    (path_to_head : g.Path start head ) -- := (extract_path_to start head state head_was_visited_before mother_invar mother_invar_adj decreasing_invar).fst)
    (ph_eq_dh : path_to_head.cost = (state.pathOrder head).1)
    (support_visited : ∀ u ∈ path_to_head.val.support, u ∈ state.visited)
    (v_not_start : v ≠ start)
    (stack_not_empty_after : ¬(dijkstra_step_expand state head tail).stack = [])
    (head_after_is_v : (dijkstra_step_expand state head tail).stack.head stack_not_empty_after = v)
    (v_visited : v ∈ state.visited)
    (the_mother : V)
    (the_mother_is : the_mother = state.mother ⟨v, v_visited⟩)
    (mother_same : (dijkstra_step_expand state head tail).mother ⟨v, v_visited_after⟩ = the_mother)
    (mother_ne_head : the_mother ≠ head)
    (mother_visited : the_mother ∈ state.visited)
    (pathOrder_unchanged : (dijkstra_step_expand state head tail).pathOrder v = state.pathOrder v)
    (adj_mother_v : g.Adj the_mother v)
    (mother_and_edge_smaller_order_before : (state.pathOrder the_mother).1 + edgeCost adj_mother_v ≤ (state.pathOrder v).1)
    (pathOrder_mother_decreases : ((dijkstra_step_expand state head tail).pathOrder the_mother).1 ≤ (state.pathOrder the_mother).1)
    (mother_not_on_stack : the_mother ∉ state.stack)
    (path_mother : Path start the_mother)
    (path_mother_is : path_mother = (extract_path_to start the_mother state mother_visited mother_invar mother_invar_adj decreasing_invar).fst)
    (v_not_in_mother_path : v ∉ path_mother.val.support)
    (path_mother_v : Path start v)
    (path_mother_v_is : path_mother_v = path_mother.concat adj_mother_v v_not_in_mother_path)
    (path_explored_contra : ∀ p : g.Path start v, (p.cost < (path_mother.concat adj_mother_v v_not_in_mother_path).cost ∧ v ∈ state.visited ∧ ∀ u ∈ p.support, u ≠ v → u ∉ state.stack ∧ u ∈ state.visited) → ⊥)
    (p' : g.Path start v)
    (p'_cheaper : p'.val.cost < path_mother_v.val.cost):
    ⊥ := by
    

      -- we can run along p' until we find a first node in p' that is still on the stack (before the expansion)
      -- or (second case) no node is on the stack, but then all nodes are visited
      have p'_elem_on_stack_or_v_visited :
        -- possibly stronger: the all elements are also visited!
        (∃ u ∈ p'.val.support, u ∈ state.stack ∧ u ≠ v ∧ (p'.support.takeWhile (· ≠ u)).all (· ∉ state.stack)) ∨
          (v ∈ state.visited ∧ ∀ u ∈ p'.val.support, u ≠ v → u ∉ state.stack ∧ u ∈ state.visited) := 
        run_path_through_state_yields_node_on_stack_or_all_visited start v v_not_start p' state start_visited on_stack_or_nei_visited

      have h1 : path_mother.cost + edgeCost adj_mother_v ≤ (state.pathOrder v).1:= by
        convert mother_and_edge_smaller_order_before
        apply eq_of_le_of_ge
        · rw [path_mother_is]
          apply dijkstra_path_extracted_not_longer_than_path_order
          exact path_order_diff
        · unfold dijkstra_stack_shortest_path at prior_invar
          specialize prior_invar the_mother mother_visited
          simp [mother_not_on_stack] at prior_invar
          unfold cost_is at prior_invar
          obtain ⟨ p, ⟨order, is_cheapest⟩ ⟩ := prior_invar
          rw [← order]
          unfold Path.is_cheapest at is_cheapest
          exact is_cheapest path_mother 
      have h2 : path_mother.cost + edgeCost adj_mother_v ≤ ((dijkstra_step_expand state head tail).pathOrder v).1 := by
        rw [pathOrder_unchanged]
        apply h1

      have h2' : path_mother_v.val.cost ≤ ((dijkstra_step_expand state head tail).pathOrder v).1 := by
        rw [path_mother_v_is]
        unfold Path.concat
        unfold Path.cost at h2
        simp
        rw [add_comm]
        exact h2


      cases p'_elem_on_stack_or_v_visited
      · next u_in_support_on_stack =>
        -- first node in p that is on the stack: call it u
        -- all nodes before u are not on the stack, i.e. paths to them are shortest paths.
        obtain ⟨u, ⟨u_in_support, ⟨ u_on_stack, u_ne_v, prior_not_on_stack⟩ ⟩ ⟩ := u_in_support_on_stack
        have u_visited : u ∈ state.visited := by grind 
        -- extract path from start to this node u
        -- su is not longer than p' itself
        obtain ⟨su, cheaper⟩ := p'.contains_subpath_cost u_in_support u_ne_v
        
        by_cases u_ne_head : head ≠ u
        · 
          apply dijkstra_shorter_path_first_on_stack_not_head (the_mother:=the_mother) (v:=v) (u:=u) (start:=start) <;> try assumption
          · exact cheaper.1
          · 
            have h3 : ((dijkstra_step_expand state head tail).pathOrder v).1 ≤ ((dijkstra_step_expand state head tail).pathOrder u).1 := by
              apply dijkstra_new_head_cost_lt_other_on_stack_now
              · unfold dijkstra_step_expand
                simp
                rw [compose] at u_on_stack
                rw [List.mem_cons] at u_on_stack
                cases u_on_stack
                case inl u_eq_head =>
                  apply absurd u_eq_head.symm u_ne_head 
                case inr u_tail =>
                  left ; assumption
              · apply head_after_is_v
            have h4 : ((dijkstra_step_expand state head tail).pathOrder u).1 ≤ (state.pathOrder u).1 := by
              unfold dijkstra_step_expand
              simp
              grind

            have h5 : ((dijkstra_step_expand state head tail).pathOrder v).1 ≤ (state.pathOrder u).1 := by omega

            omega
        · simp at u_ne_head
          rename head = u => u_eq_head
          subst u_eq_head 
          obtain ⟨u',s_u,adj_head_u',u'_v,supp1,supp2,compose⟩  := Path.recompose p' u_in_support
          have compose_early_split : p'.val = s_u.val.append (Walk.cons adj_head_u' u'_v) := by sorry
          
          have u'_ne_start : u' ≠ start := by
            by_contra
            rw [this] at supp1 
            simp at supp1

          have u'_ne_head : u' ≠ head := by
            by_contra ; subst this
            apply absurd (s_u.val.goal_in_support) supp1
          
          have p'_cost_compose : p'.val.cost = s_u.val.cost + u'_v.val.cost + g.edgeCost adj_head_u' := by
            rw [compose]
            unfold Path.append Path.concat
            simp only [Walk.append_cost, Walk.concat_inc_cost_by_edge]
            omega
          
          --rw [p'_cost_compose] at p'_cheaper
          -- w is on the stack and will remain on the stack
          have h3 : s_u.val.cost + edgeCost adj_head_u' + u'_v.val.cost < ((dijkstra_step_expand state head tail).pathOrder v).1 := by omega
          

          by_cases v_not_u' : v ≠ u'
          · by_cases u'_visited : u' ∈ state.visited
            · by_cases u'_not_on_stac : u' ∉ state.stack
              · have u'_v_elem_on_stack_or_v_visited :
                  -- possibly stronger: the all elements are also visited!
                  (∃ w ∈ u'_v.val.support, w ∈ state.stack ∧ w ≠ v ∧ (u'_v.support.takeWhile (· ≠ w)).all (· ∉ state.stack)) ∨
                    (v ∈ state.visited ∧ ∀ w ∈ u'_v.val.support, w ≠ v → w ∉ state.stack ∧ w ∈ state.visited) := 
                  run_path_through_state_yields_node_on_stack_or_all_visited u' v v_not_u' u'_v state u'_visited on_stack_or_nei_visited


                cases u'_v_elem_on_stack_or_v_visited
                · rename_i h
                  obtain ⟨w,w_in_u'_v_support,w_on_stack,w_ne_v,all_prior_not_on_stack⟩ := h
                  obtain ⟨ u'_w, cheaper, supp_subseq ⟩ := u'_v.contains_subpath_cost w_in_u'_v_support w_ne_v 

                  have head_ne_w : head ≠ w := by
                    by_contra ; subst this
                    have p'_supp_compose: p'.val.support = s_u.val.support ++ u'_v.val.support := by
                      rw [compose_early_split]
                      rw [Walk.support_of_append]
                      conv =>
                        left
                        arg 2
                        unfold Walk.support
                      simp only [List.tail_cons]
                    have head_in_su_supp : head ∈ s_u.val.support := by simp
                    --have head_in_u'v_supp : head ∈ u'_v.support := by unfold Path.support ; exact w_in_u'_v_support
                    have p'_nodup := p'.prop
                    rw [p'_supp_compose] at p'_nodup
                    apply List.nodup_append.mp at p'_nodup
                    obtain ⟨_,_,contra⟩ := p'_nodup
                    specialize contra head head_in_su_supp head w_in_u'_v_support
                    simp only [ne_eq, not_true_eq_false] at contra
                  
                  have u'_ne_w : u' ≠ w := by
                    by_contra ; subst this ; contradiction

                    --obtain ⟨before_w, _ ⟩ := u'_w.split_at_end head_ne_w 
                  obtain ⟨ before_w, u'_before_w, adj_bef_w_w, w_not_in_supp, u'_w_compose⟩ := u'_w.split_at_end u'_ne_w 

                  have no_pw_mem_on_stack : ∀ x ∈ u'_before_w.support, x ∉ state.stack := by
                    intro x x_in_support
                    unfold Path.support at all_prior_not_on_stack supp_subseq
                    rw [u'_w_compose] at supp_subseq
                    simp at supp_subseq
                    unfold List.IsPrefix at supp_subseq
                    obtain ⟨ t, compose ⟩ := supp_subseq
                    rw [← compose] at all_prior_not_on_stack
                    rw [List.append_assoc] at all_prior_not_on_stack
                    rw [List.takeWhile_append_of_pos] at all_prior_not_on_stack
                    · rw [List.all_append] at all_prior_not_on_stack
                      apply Bool.and_elim_left at all_prior_not_on_stack
                      apply List.all_iff_forall_prop.mp at all_prior_not_on_stack
                      apply all_prior_not_on_stack
                      unfold Path.support at x_in_support
                      apply x_in_support
                    · grind
                  
                  -- w now has to not be part of the stack (as u was the first node to be on the stack!)
                  have before_w_not_on_stack : before_w ∉ state.stack := by
                    apply no_pw_mem_on_stack
                    apply Walk.goal_in_support

                  have before_w_visited : before_w ∈ state.visited := by
                    apply track_path_not_on_stack (p_w := u'_before_w)
                    · exact on_stack_or_nei_visited
                    · unfold search_invar_start_visited
                      exact u'_visited
                    · exact no_pw_mem_on_stack
                    · apply Path.goal_in_support

                  have w_visited : w ∈ state.visited := by
                    unfold search_invar_on_stack_or_all_neighbours_visited at on_stack_or_nei_visited 
                    specialize on_stack_or_nei_visited ⟨ before_w, before_w_visited ⟩
                    grind
   

                  let start_before_w : g.Walk start before_w := (s_u.val.concat adj_head_u').append u'_before_w.val

                  apply dijkstra_shorter_path_with_optimal_node_and_adj_on_stack (p:=path_mother_v) (p':=p') (p'_u:=start_before_w) (u:=before_w) (u':=w)  <;> try assumption
                  · grind
                  · apply head_ne_w.symm
                  · rw [p'_cost_compose]
                    unfold start_before_w
                    have u'_v_cost : edgeCost adj_bef_w_w + u'_before_w.val.cost ≤ u'_v.val.cost := by
                      unfold Path.cost at cheaper
                      apply le_trans ; rotate_left
                      · apply cheaper
                      · rw [u'_w_compose]
                        simp
                    simp
                    omega
                  · unfold dijkstra_stack_shortest_path at prior_invar
                    specialize prior_invar before_w before_w_visited
                    simp [before_w_not_on_stack] at prior_invar
                    exact prior_invar

                -- entire path is visited and not on the stack (now all nodes on p' except for head itself)
                · rename_i h
                  obtain ⟨v_visited,all_except_v_not_on_stack_and_visited⟩ := h 
                  sorry -- path was fully on not stack and fully visited
              ·
                apply dijkstra_shorter_path_with_optimal_node_and_adj_on_stack (p:=path_mother_v) (p':=p')  (p'_u:=s_u.val) (u:=head) (u':=u')  <;> try assumption
                · by_contra head_in_tail 
                  have head_after_on_stack : head ∈ (dijkstra_step_expand state head tail).stack := by
                    unfold dijkstra_step_expand ; simp ; grind
                  
                  -- strange impossible case: head is twice on the stack. This should be impossible.
                  -- unclear how.
                  sorry
                · simp at u'_not_on_stac
                  exact u'_not_on_stac
                · rw [p'_cost_compose]
                  simp
                  omega
                · unfold dijkstra_stack_shortest_path at prior_invar
                  specialize prior_invar head (by grind)
                  rename_i _ _ stack_compose
                  rw [stack_compose] at prior_invar
                  
                  simp at prior_invar
                  exact prior_invar
            · -- u' will be on stack afterwards
              -- as u' ≠ v, it must have a path order ≥v, i.e. the update from head cause a value larger than the length of path_mover_v -- which contradicts shortestpath
              have u'_on_stack_after : u' ∈ (dijkstra_step_expand state head tail).stack := by
                unfold dijkstra_step_expand ; simp ; grind
              
              have u'_larger_order : ((dijkstra_step_expand state head tail).pathOrder v).1 ≤ ((dijkstra_step_expand state head tail).pathOrder u').1 := by
                apply dijkstra_new_head_cost_lt_other_on_stack_now <;> try assumption
              
              --have x2 : s_u.val.cost + edgeCost adj_head_u' + u'_v.val.cost < ((dijkstra_step_expand state head tail).pathOrder u').1 := by omega
              

              have updated_from_head : ((dijkstra_step_expand state head tail).pathOrder u').1 ≤ (state.pathOrder head).1 + edgeCost adj_head_u' := by
                unfold dijkstra_step_expand ; simp ; grind

              have head_optimal : s_u.val.cost ≥ (state.pathOrder head).1 := by
                specialize prior_invar head head_was_visited_before
                rename_i stack_compose
                rw [stack_compose] at prior_invar
                simp at prior_invar
                unfold cost_is at prior_invar
                obtain ⟨p,p_cost,is_cheapest⟩ := prior_invar
                unfold Path.is_cheapest at is_cheapest
                specialize is_cheapest s_u
                rw [p_cost] at is_cheapest
                unfold Path.cost at is_cheapest
                exact is_cheapest

              omega
          · simp at v_not_u' ; subst v_not_u'
            -- p' goes to head and then immediately to v
            have u'_v_cost_zero : u'_v.cost = 0 := by apply WeightedDiGraph.Path.cost_empty_zero
            unfold Path.cost at u'_v_cost_zero
            simp [u'_v_cost_zero] at p'_cost_compose h3
            -- v has been updated from head
            have  v_updated : ((dijkstra_step_expand state head tail).pathOrder v).1 ≤ (state.pathOrder head).1 + edgeCost adj_head_u' := by
              unfold dijkstra_step_expand ; simp ; grind
            have  head_optimal : (state.pathOrder head).1 ≤ s_u.val.cost := by
              unfold dijkstra_stack_shortest_path at prior_invar
              specialize prior_invar head (by grind)
              rename_i _ _ stack_compose
              rw [stack_compose] at prior_invar
              simp at prior_invar
              unfold cost_is at prior_invar
              obtain ⟨sp, cost_eq, cheapest⟩ := prior_invar
              unfold Path.is_cheapest at cheapest
              specialize cheapest s_u
              rw [cost_eq] at cheapest
              unfold Path.cost at cheapest
              exact cheapest
            omega
      -- 2. case: all nodes in p' are visited and all but v are not on the stack
      · next h =>
        -- path is completely explored, so we have the update invar along it
        have v_visited := h.left
        specialize path_explored_contra p'
        simp_all




set_option maxHeartbeats 2000000000

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
    (start_not_mem_tail : search_invar_start_not_mem_tail start state)
    :
     ∀ head : V, ∀ tail : List V, 
        dijkstra_stack_shortest_path start state
          ∧ ¬ head = goal
          ∧ state.stack = head :: tail
        → dijkstra_stack_shortest_path start (dijkstra_step_expand state head tail) := by
    intro head tail ⟨prior_invar,head_is_not_goal,compose⟩ 
    unfold dijkstra_stack_shortest_path --at prior_invar ⊢
    intro v v_visited_after not_on_stack_or_head
    
    simp at compose v_visited_after not_on_stack_or_head prior_invar ⊢



    -- properties of the current head
    have head_was_visited_before : head ∈ state.visited := by simp_all
    -- there is a path to head and it is as long as we memorised:w

    let path_to_head : g.Path start head :=
      (extract_path_to start head state head_was_visited_before mother_invar mother_invar_adj decreasing_invar).1

    -- cost of path_to_head is what we memorised
    have ph_eq_dh : path_to_head.cost = (state.pathOrder head).1 := by
      unfold dijkstra_stack_shortest_path at prior_invar
      apply eq_of_le_of_ge
      · apply dijkstra_path_extracted_not_longer_than_path_order
        exact path_order_diff
      · specialize prior_invar head head_was_visited_before
        simp_all
        unfold cost_is at prior_invar
        obtain ⟨hp, ⟨ hp_cost, hp_cheapest ⟩ ⟩ := prior_invar
        unfold Path.is_cheapest at hp_cheapest
        specialize hp_cheapest path_to_head
        rw [hp_cost] at hp_cheapest
        simp_all

    have support_visited : ∀ u ∈ path_to_head.val.support, u ∈ state.visited := by
      apply support_of_path_visited
      unfold path_to_head
      rfl



    by_cases v_not_start : v ≠ start
    · cases not_on_stack_or_head
      · next v_not_on_stack =>
        specialize prior_invar v 
        unfold dijkstra_step_expand at v_not_on_stack v_visited_after ⊢
        simp at v_visited_after
        cases v_visited_after
        · next v_was_visited =>
          simp_all 
          have invar_taut : ¬v = head ∨ head = v := by grind
          specialize prior_invar invar_taut
          grind
        · next both =>
          obtain ⟨ head_adj_v, v_was_not_visited ⟩ := both
          simp_all -- contractiction. This case is impossible
      · next v_now_stack_head =>
        simp at v_now_stack_head
        obtain ⟨ stack_not_empty_after, head_after_is_v ⟩ := v_now_stack_head
        --unfold dijkstra_step_expand at stack_not_empty_after head_after_is_v v_visited_after ⊢
        unfold cost_is
        

        by_cases v_visited : v ∈ state.visited
        · 
          -- v is *now* the head of the stack, but it was already visited before.
          -- this means it had to already have been on the stack before

          -- TODO: split on what the mother of v now is
          -- if it is the old mothe, by decreasing invar, it cannot be on the stack (its order must be lower than v's)
          -- so we have a shortest path to it: its order is equal to that path. We extend by one.
          -- XXX: maybe have to prove that my order is still mother + edge ...????
          -- if it is head, then we have a shortest path to it
          -- then we got updated and we know our own pathOrder.
          have mother_options := dijkstra_mother_options state head tail ⟨v,v_visited⟩ v_visited_after
          cases mother_options
          case pos.inl mother_is_head =>
            have adj_head_v : g.Adj head v := by 
              unfold dijkstra_step_expand at mother_is_head
              unfold search_invar_mother_is_adjacent at mother_invar_adj
              specialize mother_invar_adj ⟨ v, v_visited ⟩ v_not_start
              grind
            
            have v_ne_head : v ≠ head := by
              by_contra v_eq_head
              subst v_eq_head
              unfold dijkstra_step_expand at mother_is_head
              unfold search_invar_mother_decreasing_path_order at decreasing_invar
              specialize decreasing_invar ⟨ v, v_visited ⟩ v_not_start
              simp_all
              apply FValueComp.lt_irr (state.pathOrder v) decreasing_invar

            let e := edgeCost adj_head_v
            have v_order_eq_head_plus_edge : ((dijkstra_step_expand state head tail).pathOrder v).1 = ((dijkstra_step_expand state head tail).pathOrder head).1 + e := by
              unfold dijkstra_step_expand at mother_is_head ⊢
              simp_all
              grind

            have v_not_mem_ph_support : v ∉ ↑path_to_head.val.support := by 
              by_contra v_in_support
              have h := (extract_path_to start head state head_was_visited_before mother_invar mother_invar_adj decreasing_invar).2
              specialize h v (by apply v_in_support) v_ne_head
              unfold dijkstra_step_expand at v_order_eq_head_plus_edge mother_is_head
              simp_all
              have v_visited : v ∈ state.visited := by grind
              unfold search_invar_mother_decreasing_path_order at decreasing_invar
              specialize decreasing_invar ⟨ v, v_visited ⟩ v_not_start
              split_ifs at v_order_eq_head_plus_edge <;> (try  grind)
              · simp_all
                have order_eq := FValueComp.lt_antisymm (state.pathOrder head) (state.pathOrder v) decreasing_invar h
                rw [order_eq] at h
                apply FValueComp.lt_irr (state.pathOrder v) h
              · simp_all
                have order_eq := FValueComp.lt_antisymm (state.pathOrder head) (state.pathOrder v) decreasing_invar h
                rw [order_eq] at h
                apply FValueComp.lt_irr (state.pathOrder v) h
              · simp_all
                have order_eq := FValueComp.lt_antisymm (state.pathOrder head) (state.pathOrder v) decreasing_invar h
                rw [order_eq] at h
                apply FValueComp.lt_irr (state.pathOrder v) h
              all_goals
                rename_i a b c
                unfold edgeCost at c v_order_eq_head_plus_edge
                unfold FValueComp.lt Nat.instFValueCompProd at h
                simp_all
                apply Prod.lex_iff.mp at h
                cases h
                · grind
                next prop =>
                  obtain ⟨ eq, lt ⟩ := prop
                  have e_zero : e = 0 := by omega
                  simp_all
                  have o_eq : state.pathOrder v = ((state.pathOrder head).1, (state.pathOrder head).2 + 1) := by grind
                  specialize mother_is_head o_eq
                  grind

            let path_to_v : g.Path start v := path_to_head.concat adj_head_v v_not_mem_ph_support 

            use path_to_v
            constructor
            · unfold path_to_v
              rw [WeightedDiGraph.Path.concat_inc_cost_by_edge]
              unfold dijkstra_step_expand
              simp_all
              unfold edgeCost
              rw [add_comm]
              split_ifs <;> try grind
              rename_i v_lt_head_edge
              unfold dijkstra_step_expand at v_order_eq_head_plus_edge
              simp_all
              unfold e edgeCost at v_order_eq_head_plus_edge
              split_ifs at v_order_eq_head_plus_edge <;> grind
            · apply dijkstra_path_head_adj_new_head_is_cheapest <;> try assumption
              --· apply start_visited
              --· exact stack_visited_invar
              --· exact on_stack_or_nei_visited
              --· exact update_invar
              --· exact start_path_order
              --· exact prior_invar
              --· exact compose
              --· exact head_was_visited_before
              --· exact ph_eq_dh
              --· exact v_not_start
              --· exact head_after_is_v
              --· exact v_order_eq_head_plus_edge
              --· exact support_visited
              · intro p_start_v ⟨p_lt_ph_e,v_visited,cond3⟩
                obtain ⟨ w,path_start_w,w_adj_v,v_not_earlier_in_path,p_start_v_compose⟩ := p_start_v.split_at_end (Ne.symm v_not_start)
                
                have w_ne_v : w ≠ v := by
                  by_contra w_eq_v
                  rw [← w_eq_v] at v_not_earlier_in_path
                  have w_in_supp : w ∈ path_start_w.val.support := Path.goal_in_support path_start_w
                  contradiction


                have p_start_v_cost : p_start_v.val.cost = edgeCost w_adj_v + path_start_w.val.cost := by
                  rw [p_start_v_compose] ; simp
               
                have w_in_supp : w ∈ p_start_v.val.support := by rw [p_start_v_compose] ; simp
                have w_visited : w ∈ state.visited := by specialize cond3 w w_in_supp w_ne_v ; exact cond3.right
                have w_ne_mem_stack : w ∉ state.stack := by specialize cond3 w w_in_supp w_ne_v ; exact cond3.left
                
                have w_order_eq : (state.pathOrder w).1 ≤ path_start_w.val.cost := by
                  unfold dijkstra_stack_shortest_path at prior_invar
                  specialize prior_invar w w_visited
                  simp_all
                  unfold cost_is at prior_invar
                  obtain ⟨sp, ⟨ cost_eq_order, cheapest⟩ ⟩ := prior_invar
                  unfold Path.is_cheapest at cheapest
                  specialize cheapest path_start_w
                  rw [cost_eq_order] at cheapest
                  apply cheapest

                have v_updated_from_w : (state.pathOrder v).1 ≤ (state.pathOrder w).1 + edgeCost w_adj_v := by
                  unfold dijkstra_invar_on_stack_or_all_neighbours_max_order at update_invar
                  specialize update_invar ⟨ w, w_visited ⟩  w_ne_mem_stack v w_adj_v
                  exact update_invar

                conv at p_lt_ph_e => left ; unfold Path.cost
      

                have t_1 : (state.pathOrder v).1 ≤ path_start_w.val.cost + edgeCost w_adj_v := by omega
                have t_2 : (state.pathOrder v).1 ≤ p_start_v.val.cost := by omega
                have t_3 : (state.pathOrder v).1 < (path_to_head.concat adj_head_v v_not_mem_ph_support).cost := by omega
                unfold Path.concat at t_3
                simp at t_3
                unfold Path.cost at ph_eq_dh
                rw [ph_eq_dh] at t_3
                unfold dijkstra_step_expand at v_order_eq_head_plus_edge
                simp_all
                split_ifs at v_order_eq_head_plus_edge <;> omega
              · intro w' w'_ne_head adj_head_w' p ⟨ p_h_w_lt_e, v_visited, all_visited_not_mem_stack⟩
                have v_ne_w' : v ≠ w' := by grind 
                obtain ⟨ w,path_w'_w,w_adj_v,v_not_earlier_in_path,p_start_v_compose⟩ := p.split_at_end (Ne.symm v_ne_w')
                have w_ne_v : w ≠ v := by
                  by_contra w_eq_v
                  rw [← w_eq_v] at v_not_earlier_in_path
                  have w_in_supp : w ∈ path_w'_w.val.support := Path.goal_in_support path_w'_w
                  contradiction


                have p_start_v_cost : p.val.cost = edgeCost w_adj_v + path_w'_w.val.cost := by
                  rw [p_start_v_compose] ; simp
               
                have w_in_supp : w ∈ p.val.support := by rw [p_start_v_compose] ; simp
                have w_visited : w ∈ state.visited := by specialize all_visited_not_mem_stack w w_in_supp w_ne_v ; exact all_visited_not_mem_stack.right
                have w_ne_mem_stack : w ∉ state.stack := by specialize all_visited_not_mem_stack w w_in_supp w_ne_v ; exact all_visited_not_mem_stack.left
               

                --have w'_not_mem_support : w' ∉ path_to_head.val.support := by
              
                --have w'_w_nodup : (∀ a ∈ (path_to_head.concat adj_head_w' w'_not_mem_support).val.support, ∀ b ∈ path_w'_w.val.support.tail, a ≠ b) := by
                

                let walk_start_head_w' := path_to_head.val.concat adj_head_w' 
                let walk_start_head_w'_w := walk_start_head_w'.append path_w'_w.val
                
                --have w'_v_nodup : (∀ a ∈ path_start_head_w'.val.support, ∀ b ∈ p.val.support.tail, a ≠ b) := by 
                let walk_start_head_w'_v := walk_start_head_w'.append p.val

                have path_start_head_w'_length : walk_start_head_w'.cost = (state.pathOrder head).1 + edgeCost adj_head_w' := by
                  unfold walk_start_head_w'
                  simp_all [add_comm]

                have path_start_head_w'_w_length : walk_start_head_w'_w.cost = (state.pathOrder head).1 + edgeCost adj_head_w' + path_w'_w.val.cost := by
                  unfold walk_start_head_w'_w
                  simp_all
                have path_start_head_w'_v_length : walk_start_head_w'_v.cost = walk_start_head_w'.cost + p.val.cost := by 
                  unfold walk_start_head_w'_v
                  simp_all



                have w_order_eq : (state.pathOrder w).1 ≤ walk_start_head_w'_w.cost := by
                  unfold dijkstra_stack_shortest_path at prior_invar
                  specialize prior_invar w w_visited
                  unfold cost_is at prior_invar
                  simp [w_ne_mem_stack] at prior_invar
                  obtain ⟨sp, ⟨ cost_eq_order, cheapest⟩ ⟩ := prior_invar
                  unfold Path.is_cheapest at cheapest
                  simp at cheapest
                  obtain ⟨ _, cheapest ⟩ := cheapest
                  -- argument: from the walk, we can get a shorter path and even that is longer than pathOrder w
                  obtain ⟨ p', p'_leq_w'⟩ := walk_start_head_w'_w.cheaper_path_exists 

                  specialize cheapest p' p'.prop
                  rw [cost_eq_order] at cheapest
                  apply le_trans
                  · apply cheapest
                  · apply p'_leq_w'

                have v_updated_from_w : (state.pathOrder v).1 ≤ (state.pathOrder w).1 + edgeCost w_adj_v := by
                  unfold dijkstra_invar_on_stack_or_all_neighbours_max_order at update_invar
                  specialize update_invar ⟨ w, w_visited ⟩  w_ne_mem_stack v w_adj_v
                  exact update_invar

                have v_not_in_supp : v ∉ path_to_head.val.support := by grind 
                let p_start_v : g.Path start v := path_to_head.concat adj_head_v v_not_in_supp
                have p_start_v_cost : p_start_v.val.cost = path_to_head.val.cost + edgeCost adj_head_v := by
                  unfold p_start_v
                  unfold Path.concat
                  simp_all [add_comm]

                have t_1 : (state.pathOrder v).1 ≤ walk_start_head_w'_w.cost + edgeCost w_adj_v := by omega
                have t_2 : (state.pathOrder v).1 ≤ (state.pathOrder head).1 + edgeCost adj_head_w' + path_w'_w.val.cost + edgeCost w_adj_v := by omega
                have t_3 : (state.pathOrder v).1 ≤ (state.pathOrder head).1 + p.val.cost + edgeCost adj_head_w' := by omega
                unfold Path.cost at p_h_w_lt_e
                have t_4 : (state.pathOrder v).1 < (state.pathOrder head).1 + edgeCost adj_head_v := by omega
                --have t_3 : (state.pathOrder v).1 < (path_to_head.concat adj_head_v v_not_mem_ph_support).cost := by omega
                --unfold Path.concat at t_3
                --simp at t_3
                unfold Path.cost at ph_eq_dh
                --rw [ph_eq_dh] at t_3
                unfold dijkstra_step_expand at v_order_eq_head_plus_edge
                simp_all
                unfold e at v_order_eq_head_plus_edge
                split_ifs at v_order_eq_head_plus_edge <;> try omega
                all_goals
                  grind
          -- second case: the mother of v is not head, but the mother that it had before
          -- (i.e. update from head did not change anything)
-- second case: the mother of v is not head, but the mother that it had before
          -- (i.e. update from head did not change anything)
          · obtain ⟨mother_same, mother_ne_head⟩ := ‹_›
            let the_mother := state.mother ⟨v, v_visited⟩
            have mother_visited : the_mother ∈ state.visited := by
              unfold search_invar_mother_is_visited at mother_invar
              specialize mother_invar ⟨ v, v_visited ⟩
              grind
            have pathOrder_unchanged : (dijkstra_step_expand state head tail).pathOrder v = state.pathOrder v := by
              unfold dijkstra_step_expand at mother_same ⊢
              grind
            have adj_mother_v : g.Adj the_mother v := by
              unfold search_invar_mother_is_adjacent at mother_invar_adj
              specialize mother_invar_adj ⟨ v, v_visited ⟩
              grind

            have mother_and_edge_smaller_order_before : (state.pathOrder the_mother).1 + edgeCost adj_mother_v ≤ (state.pathOrder v).1 := by
              unfold dijkstra_path_order_diff_by_edge_cost at path_order_diff
              specialize path_order_diff mother_invar_adj v v_visited v_not_start
              unfold the_mother
              grind
            
            have pathOrder_mother_decreases : ((dijkstra_step_expand state head tail).pathOrder the_mother).1 ≤ (state.pathOrder the_mother).1 := by
              unfold dijkstra_step_expand
              simp_all
              grind
            

            have mother_not_on_stack : the_mother ∉ state.stack := by
              unfold dijkstra_step_expand at mother_same
              simp_all
              constructor
              · grind
              · by_contra mother_in_tail 
                have mother_neq_v : the_mother ≠ v := by
                  intro h
                  specialize decreasing_invar ⟨v, v_visited⟩ (by simp_all)
                  simp at decreasing_invar 
                  nth_rewrite 2 [← h] at decreasing_invar
                  exact FValueComp.lt_irr _ decreasing_invar
                have mother_now_geq :((dijkstra_step_expand state head tail).pathOrder the_mother).1 ≥ ((dijkstra_step_expand state head tail).pathOrder v).1 := by 
                  unfold dijkstra_step_expand at head_after_is_v
                  simp_all
                  apply mergeSort_head_from_head_unsorted at head_after_is_v
                  · specialize head_after_is_v the_mother (by simp; left ; exact mother_in_tail)
                    cases head_after_is_v
                    case inl mother_v => contradiction
                    case inr h =>
                      unfold dijkstra_step_expand
                      simp_all
                      split_ifs
                      all_goals
                        simp_all
                        split_ifs at h
                        all_goals
                          cases h
                          · grind
                          · rename_i r
                            unfold FValueComp.lt_B Nat.instFValueCompProd at r
                            simp at r
                            grind
                  · intros; apply dijkstra_merge_trans <;> assumption
                  · intros; apply dijkstra_merge_total

                have mother_now_geq_v_bef :((dijkstra_step_expand state head tail).pathOrder the_mother).1 ≥ (state.pathOrder v).1 := by grind

                by_cases zero_cost_edge : edgeCost adj_mother_v = 0
                · 
                  have mother_le_order_before : (state.pathOrder the_mother).1 ≤ (state.pathOrder v).1 := by omega
                  have mother_ge_order_before : (state.pathOrder the_mother).1 ≥ (state.pathOrder v).1 := by omega
                  have mother_eq_order_before : (state.pathOrder the_mother).1 = (state.pathOrder v).1 := by omega
                  
                  clear mother_le_order_before mother_ge_order_before
                  unfold dijkstra_step_expand at head_after_is_v
                  simp_all
                  apply mergeSort_head_from_head_unsorted at head_after_is_v
                  · specialize head_after_is_v the_mother (by simp; left ; exact mother_in_tail)
                    cases head_after_is_v
                    case pos.inl mother_v => contradiction
                    case pos.inr h =>
                      
                      unfold search_invar_mother_decreasing_path_order at decreasing_invar 
                      specialize decreasing_invar ⟨ v , v_visited ⟩ v_not_start
                      unfold FValueComp.lt Nat.instFValueCompProd at decreasing_invar
                      simp at decreasing_invar
                      apply Prod.lex_iff.mp at decreasing_invar
                      have p' : (state.pathOrder (state.mother ⟨v, v_visited⟩)).2 < (state.pathOrder v).2 := by grind

                      simp_all
                      split_ifs at h
                      rotate_left 9
                      · simp_all
                        cases h
                        · try simp_all
                          grind
                        · rename_i r
                          unfold FValueComp.lt_B Nat.instFValueCompProd at r
                          simp at r
                          apply Prod.lex_iff.mp at r
                          have p : (state.pathOrder v).2 < (state.pathOrder the_mother).2 := by
                            cases r
                            case inl h =>
                              simp_all
                              rename_i a b c
                              unfold edgeCost at a b c h mother_eq_order_before decreasing_invar
                              have adj_head_v : g.Adj head v := by grind
                              have adj_head_mother : g.Adj head the_mother := by grind
                              
                              by_cases edgeCost adj_head_v = edgeCost adj_head_mother
                              · rename_i cost_eq
                                specialize b (by unfold edgeCost at cost_eq ; grind) 
                                unfold dijkstra_step_expand at pathOrder_unchanged
                                simp at pathOrder_unchanged
                                unfold edgeCost at pathOrder_unchanged
                                specialize pathOrder_unchanged adj_head_v
                                simp [*] at pathOrder_unchanged
                                have h : (state.pathOrder head).2 + 1 = (state.pathOrder v).2 := by grind
                                grind
                              · have v_lt_m : edgeCost adj_head_v < edgeCost adj_head_mother := by 
                                  rename_i neq
                                  unfold edgeCost at neq ⊢
                                  grind 
                                unfold dijkstra_step_expand at pathOrder_unchanged
                                simp at pathOrder_unchanged
                                unfold edgeCost at pathOrder_unchanged
                                specialize pathOrder_unchanged adj_head_v
                                simp [*] at pathOrder_unchanged
                                specialize pathOrder_unchanged (by grind)
                                have h : (state.pathOrder head).2 + 1 = (state.pathOrder v).2 := by grind
                                grind
                            · grind
                          clear r
                          unfold the_mother at p
                          omega
                      all_goals
                        simp_all
                        cases h
                        · simp_all
                          try grind
                        · rename_i r
                          unfold FValueComp.lt_B Nat.instFValueCompProd at r
                          simp at r
                          apply Prod.lex_iff.mp at r
                          have p : (state.pathOrder v).2 < (state.pathOrder the_mother).2 := by grind
                          clear r
                          unfold the_mother at p
                          omega
                  · intros; apply dijkstra_merge_trans <;> assumption
                  · intros; apply dijkstra_merge_total
    
                · have mother_smaller_order_before : (state.pathOrder the_mother).1 < (state.pathOrder v).1 := by omega
                  have mother_now_smaller_order_before : ((dijkstra_step_expand state head tail).pathOrder the_mother).1 < ((dijkstra_step_expand state head tail).pathOrder v).1 := by grind
                  have mother_now_geq :((dijkstra_step_expand state head tail).pathOrder the_mother).1 ≥ ((dijkstra_step_expand state head tail).pathOrder v).1 := by 
                    unfold dijkstra_step_expand at head_after_is_v
                    simp_all
                  omega

            -- path to v is the path it was before. This will be a path to its mother and then that edge
            let path_mother := (extract_path_to start the_mother state mother_visited mother_invar mother_invar_adj decreasing_invar).1


            have v_not_in_mother_path : v ∉ path_mother.val.support := by
              intro v_in_path_mother
              have path_order := (extract_path_to start the_mother state mother_visited 
                mother_invar mother_invar_adj decreasing_invar).2
              -- v ≠ the_mother (since pathOrder the_mother ≺ pathOrder v, so they differ)
              have v_ne_mother : v ≠ the_mother := by
                intro h--; subst h
                have decr := decreasing_invar ⟨v, v_visited⟩ v_not_start
                simp at decr
                nth_rewrite 2 [h] at decr
                exact FValueComp.lt_irr _ decr
              -- extract_path_to .2: pathOrder v ≺ pathOrder the_mother
              have pv_lt_pm := path_order v v_in_path_mother v_ne_mother
              -- decreasing_invar: pathOrder the_mother ≺ pathOrder v
              have pm_lt_pv := decreasing_invar ⟨v, v_visited⟩ v_not_start
              -- cycle: pathOrder v ≺ pathOrder the_mother ≺ pathOrder v
              exact FValueComp.lt_irr _ (FValueComp.lt_trans _ _ _ pv_lt_pm pm_lt_pv)
            let path_mother_v := path_mother.concat adj_mother_v v_not_in_mother_path

            use path_mother_v
            constructor
            · rw [pathOrder_unchanged]
              unfold path_mother_v
              rw [Path.concat_inc_cost_by_edge]
              apply eq_of_le_of_ge
              · have original_path_order_diff := path_order_diff
                unfold dijkstra_path_order_diff_by_edge_cost at path_order_diff
                specialize path_order_diff mother_invar_adj v v_visited v_not_start
                apply le_trans ; rotate_left
                · apply path_order_diff
                · nth_rewrite 1 [add_comm]
                  apply add_le_add_left
                  unfold path_mother
                  apply dijkstra_path_extracted_not_longer_than_path_order
                  exact original_path_order_diff
              · unfold dijkstra_invar_on_stack_or_all_neighbours_max_order at update_invar
                specialize update_invar ⟨ the_mother, mother_visited ⟩ mother_not_on_stack v adj_mother_v
                rw [add_comm]
                apply le_trans
                · apply update_invar
                · apply add_le_add_left
                  unfold dijkstra_stack_shortest_path at prior_invar
                  specialize prior_invar the_mother
                  simp_all
                  unfold cost_is at prior_invar
                  obtain ⟨ p, p_cost, is_cheapest ⟩ := prior_invar
                  unfold Path.is_cheapest at is_cheapest
                  specialize is_cheapest path_mother
                  unfold Path.cost at is_cheapest p_cost
                  convert is_cheapest
                  exact p_cost.symm
            · rename_i h 
              obtain ⟨ mother_remains, mother_ne_head ⟩ := h
              unfold Path.is_cheapest
              intro p'
              by_contra p'_cheaper; simp at p'_cheaper
              have pm_eq_dm : path_mother.val.cost = (state.pathOrder the_mother).1 := by
                sorry

              apply dijkstra_path_mother_adj_new_head_is_cheapest (start:=start) (v:=v) (p':=p') (path_mother:=path_mother) <;> try assumption
              · rfl
              · unfold path_mother ; rfl
              · unfold path_mother_v ; rfl
              · intro p_start_v ⟨p_lt_ph_e,v_visited,cond3⟩
                obtain ⟨ w,path_start_w,w_adj_v,v_not_earlier_in_path,p_start_v_compose⟩ := p_start_v.split_at_end (Ne.symm v_not_start)
                
                have w_ne_v : w ≠ v := by
                  by_contra w_eq_v
                  rw [← w_eq_v] at v_not_earlier_in_path
                  have w_in_supp : w ∈ path_start_w.val.support := Path.goal_in_support path_start_w
                  contradiction


                have p_start_v_cost : p_start_v.val.cost = edgeCost w_adj_v + path_start_w.val.cost := by
                  rw [p_start_v_compose] ; simp
               
                have w_in_supp : w ∈ p_start_v.val.support := by rw [p_start_v_compose] ; simp
                have w_visited : w ∈ state.visited := by specialize cond3 w w_in_supp w_ne_v ; exact cond3.right
                have w_ne_mem_stack : w ∉ state.stack := by specialize cond3 w w_in_supp w_ne_v ; exact cond3.left
                
                have w_order_eq : (state.pathOrder w).1 ≤ path_start_w.val.cost := by
                  unfold dijkstra_stack_shortest_path at prior_invar
                  specialize prior_invar w w_visited
                  simp_all
                  unfold cost_is at prior_invar
                  obtain ⟨sp, ⟨ cost_eq_order, cheapest⟩ ⟩ := prior_invar
                  unfold Path.is_cheapest at cheapest
                  specialize cheapest path_start_w
                  rw [cost_eq_order] at cheapest
                  apply cheapest

                have v_updated_from_w : (state.pathOrder v).1 ≤ (state.pathOrder w).1 + edgeCost w_adj_v := by
                  unfold dijkstra_invar_on_stack_or_all_neighbours_max_order at update_invar
                  specialize update_invar ⟨ w, w_visited ⟩  w_ne_mem_stack v w_adj_v
                  exact update_invar

                conv at p_lt_ph_e => left ; unfold Path.cost
      

                have t_1 : (state.pathOrder v).1 ≤ path_start_w.val.cost + edgeCost w_adj_v := by omega
                have t_2 : (state.pathOrder v).1 ≤ p_start_v.val.cost := by omega
                have t_3 : (state.pathOrder v).1 < (path_mother.concat adj_mother_v v_not_in_mother_path).cost := by omega
                unfold Path.concat at t_3
                simp at t_3
                unfold Path.cost at ph_eq_dh
                rw [pm_eq_dm] at t_3
                omega
        · unfold dijkstra_step_expand at v_visited_after
          simp at v_visited_after
          simp [v_visited] at v_visited_after

          let e := edgeCost v_visited_after
          have v_order_eq_head_plus_edge : ((dijkstra_step_expand state head tail).pathOrder v).1 = ((dijkstra_step_expand state head tail).pathOrder head).1 + e := by
            unfold dijkstra_step_expand
            simp_all
            grind

          let path_to_v : g.Path start v := path_to_head.concat v_visited_after (by
            by_contra v_in_support
            have v_visited_before := support_visited v v_in_support
            contradiction)


          use path_to_v
          constructor
          · unfold path_to_v
            rw [WeightedDiGraph.Path.concat_inc_cost_by_edge]
            unfold dijkstra_step_expand
            simp_all
            unfold edgeCost
            rw [add_comm]
          · -- Situation: v is head of stack after expansion of head
            -- v was added to the stack due to expansion of v (i.e. it was not visited before)
            -- ph (path_to_head) is a shortest path to head
            -- selected apth to v is (path_to_head ; <head,v>)
            -- 
            -- Now: Assume there is a shorter path to v: p'
            apply dijkstra_path_head_adj_new_head_is_cheapest <;> try assumption
            · grind
            · grind
    · simp at v_not_start
      subst v_not_start
      apply dijkstra_expand_keeps_shortest_path_invar_start
      · exact start_visited
      · exact start_path_order
      · apply head_is_not_goal
      · exact compose




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
          · exact invar_before.right.right.right.right.right.left
          · exact invar_before.right.right.right.right.right.right
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
          · exact ⟨ invar_before.right.right.right.right.right.left, head_ne_goal, compose⟩
        · apply dijkstra_expand_start_not_mem_tail_carries 
          · exact invar_before.left.right.right.right.right.right
          · exact invar_before.right.right.right.right.right.left
          · exact ⟨ invar_before.right.right.right.right.right.right, head_ne_goal, compose⟩



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
