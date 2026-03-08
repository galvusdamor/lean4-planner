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
------ astar implementation and proof ------


--abbrev astar_search_state (g : NatGraph V) := WeightedDiGraph.base_search_state g (ℕ × Fin g.nodeNum)
abbrev astar_search_state (g : NatGraph V) := WeightedDiGraph.base_search_state g (ℕ × ℕ)

    
@[simp]
def path_val (priorState : astar_search_state g) (cur v : V) (adj : g.Adj cur v) : (ℕ × ℕ) := 
  ⟨ (priorState.pathOrder cur).fst + g.edgeCost adj, (priorState.pathOrder cur).snd + 1⟩

@[simp]
def new_cost (priorState : astar_search_state g) (cur v : V) (adj : g.Adj cur v) :=
  if (priorState.pathOrder v).1 < (path_val priorState cur v adj).1 then 
    (priorState.pathOrder v)
  else if (priorState.pathOrder v).1 = (path_val priorState cur v adj).1 ∧ (priorState.pathOrder v).2 < (path_val priorState cur v adj).2 then 
    (priorState.pathOrder v)
  else
    (path_val priorState cur v adj)

@[simp]
def add_heur (v : V) (p : ℕ × ℕ) (heur : V → ℕ) : ℕ × ℕ := ⟨p.1 + heur v, p.2⟩ 

def astar_step_expand
    (heur : V → ℕ)
    (priorState : astar_search_state g)
    (stackHead : V)
    (stackTail : List V):
    (astar_search_state g) :=
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

     let new_stack : List V := (stackTail ++ newly_visited_list).mergeSort (fun a b =>
        add_heur a (new_order a) heur = add_heur b (new_order b) heur || FValueComp.lt_B (add_heur a (new_order a) heur) (add_heur b (new_order b) heur)) 
       
     WeightedDiGraph.base_search_state.mk new_visited new_order new_mother new_stack


def astar_termination_metric 
    (s : astar_search_state g): (Vector (WithTop (ℕ × ℕ)) g.nodeNum) × ℕ :=
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

variable (heur : V → ℕ)

lemma astar_expand_metric_reduction : WeightedDiGraph.termination_proof_for_expand (G:=g) (state_type := astar_search_state g) (D:=ℕ ×ℕ) (astar_step_expand heur) goal astar_termination_metric := by
    unfold WeightedDiGraph.termination_proof_for_expand
    intro state head tail ⟨head_ne_goal,compose⟩
    unfold WellFoundedRelation.rel
    unfold instWellFoundedRelationProdVectorWithTopNat_graphlib
    apply Prod.lex_iff.mpr
    apply (Classical.or_iff_not_imp_left).mpr
    contrapose
    rw [not_and]
    intro x
    by_cases eq : (astar_termination_metric (astar_step_expand heur state head tail)).1 = (astar_termination_metric state).1
    · specialize x eq
      unfold astar_termination_metric astar_step_expand at x
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
      unfold astar_step_expand astar_termination_metric at eq
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
        unfold astar_termination_metric astar_step_expand at not_lex not_eq
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




lemma astar_expand_newly_added_are_adjacent 
    (priorState : astar_search_state g)
    (stackHead : V)
    (stackTail : List V):
    ∀ x : V, x ∉ priorState.visited ∧ x ∉ stackTail ∧
      x ∈ (astar_step_expand heur priorState stackHead stackTail).stack →  
      g.Adj stackHead x := by
    intro x ⟨x_not_visi, ⟨ x_not_on_stack_before, x_on_stack_after ⟩  ⟩
    unfold astar_step_expand at x_on_stack_after
    simp_all


lemma astar_expand_keeps_stack_in_visited 
    (priorState : astar_search_state  g)
    (stackHead : V)
    (stackTail : List V):
    WeightedDiGraph.search_invar_stack_is_visited priorState ∧
      stackHead ∈ priorState.visited ∧ (∀ x : V, x ∉ priorState.visited → x ∉ stackTail) →
      WeightedDiGraph.search_invar_stack_is_visited (astar_step_expand heur priorState stackHead stackTail) := by
      intro ⟨ stack_is_visited_prior, stackhead_visited, x_not_in_stack_tail⟩ 
      unfold WeightedDiGraph.search_invar_stack_is_visited
      intro x x_now_on_stack
      unfold astar_step_expand
      simp_all
      by_cases x_was_visited : x ∈ priorState.visited
      · left
        exact x_was_visited
      · right
        have adj : g.Adj stackHead x := by 
          apply (astar_expand_newly_added_are_adjacent heur priorState stackHead stackTail)
          simp_all
        use adj ; left ; exact x_was_visited


lemma astar_expand_keeps_mother_in_visited 
    (priorState : astar_search_state  g)
    (stackHead : V)
    (stackTail : List V):
    WeightedDiGraph.search_invar_mother_is_visited priorState ∧ stackHead ∈ priorState.visited → WeightedDiGraph.search_invar_mother_is_visited (astar_step_expand heur priorState stackHead stackTail) := by
      intro mother_is_visited_prior
      unfold WeightedDiGraph.search_invar_mother_is_visited
      intro x
      by_cases mother_becomes_head : (astar_step_expand heur priorState stackHead stackTail).mother x = stackHead
      · rw [mother_becomes_head]
        unfold astar_step_expand
        simp_all
      · have x_was_visited : x.val ∈ priorState.visited := by
          obtain ⟨ x', x_now_visi ⟩ := x
          unfold astar_step_expand at mother_becomes_head x_now_visi
          simp at x_now_visi
          cases x_now_visi
          · simp_all
          · simp_all
            rename_i h
            obtain ⟨ adj, p ⟩ := h
            cases p <;> simp_all
        have mother_unchanged : 
          (astar_step_expand heur priorState stackHead stackTail).mother x = priorState.mother ⟨ x.val, x_was_visited ⟩ := by
          unfold astar_step_expand at mother_becomes_head ⊢ 
          simp_all
        rw [mother_unchanged]
        unfold astar_step_expand
        simp_all


lemma astar_expand_keeps_mother_is_adjacent
    (start : V)
    (priorState : astar_search_state  g)
    (stackHead : V)
    (stackTail : List V):
    WeightedDiGraph.search_invar_mother_is_adjacent start priorState → WeightedDiGraph.search_invar_mother_is_adjacent start (astar_step_expand heur priorState stackHead stackTail) := by
      intro mother_is_adjacent_prior
      unfold WeightedDiGraph.search_invar_mother_is_adjacent
      intro x
      simp_all
      intro x_not_start
      unfold astar_step_expand
      simp_all
      split
      next adj_decide_true =>
        split <;> split <;> grind
      · next x_not_prior_visited => 
        obtain ⟨ xx, x_in_new_visited ⟩ := x
        unfold astar_step_expand at x_in_new_visited
        simp at x_in_new_visited
        simp_all



lemma astar_mother_options
    (priorState : astar_search_state  g)
    (stackHead : V)
    (stackTail : List V)
    (x : priorState.visited)
    (x_still_visited : x.val ∈ (astar_step_expand heur priorState stackHead stackTail).visited):
      ((astar_step_expand heur priorState stackHead stackTail).mother ⟨x.val, x_still_visited⟩) = stackHead ∨
      (((astar_step_expand heur priorState stackHead stackTail).mother ⟨x.val, x_still_visited⟩) = (priorState.mother x) ∧ (priorState.mother x) ≠ stackHead)
      := by 
        unfold astar_step_expand
        grind


set_option maxHeartbeats 1000000


/-- TODO: externalise haves into helpter theorems
--/ 
lemma astar_expand_keeps_mother_ordered 
    (start : V)
    (priorState : astar_search_state  g)
    (stackHead : V)
    (stackTail : List V):
    WeightedDiGraph.search_invar_mother_is_visited priorState ∧
      stackHead ∈ priorState.visited ∧ 
      WeightedDiGraph.search_invar_mother_decreasing_path_order start priorState
      ∧ WeightedDiGraph.search_invar_mother_is_visited priorState 
      → WeightedDiGraph.search_invar_mother_decreasing_path_order start
          (astar_step_expand heur priorState stackHead stackTail)
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
      unfold astar_step_expand at a_now_visited
      grind

    have was_visited_if_not_adj : 
      ∀ x ∈ (astar_step_expand heur priorState stackHead stackTail).visited, ¬ g.Adj stackHead x → x ∈ priorState.visited := by
      intro x now_visited not_adj
      unfold astar_step_expand at now_visited
      grind

    have h_order : ∀ x : V, ¬ g.Adj stackHead x → priorState.pathOrder x = (astar_step_expand heur priorState stackHead stackTail).pathOrder x := by 
      intro x ne_adj_head
      unfold astar_step_expand
      grind

    have h_mother : ∀ x : (astar_step_expand heur priorState stackHead stackTail).visited, ∀ ne_adj : ¬ g.Adj stackHead x, priorState.mother ⟨↑x, was_visited_if_not_adj x.val x.prop ne_adj ⟩ = (astar_step_expand heur priorState stackHead stackTail).mother x := by 
      intro x ne_adj_head
      unfold astar_step_expand
      grind
    
    have h_dec_1 :
      ∀ x ∈ priorState.visited, ((astar_step_expand heur priorState stackHead stackTail).pathOrder x).1 ≤ (priorState.pathOrder x).1:= by 
      intro x
      unfold astar_step_expand
      simp_all
      split_ifs <;> simp_all

    have h_dec_2 :
      ∀ x ∈ priorState.visited, ((astar_step_expand heur priorState stackHead stackTail).pathOrder x).1 = (priorState.pathOrder x).1 → ((astar_step_expand heur priorState stackHead stackTail).pathOrder x).2 ≤ (priorState.pathOrder x).2:= by 
      intro x
      unfold astar_step_expand
      simp_all
      split_ifs <;> simp_all

    have h_new_visi :
      ∀ x : V, ∀ adj : g.Adj stackHead x, x ∉ priorState.visited → ((astar_step_expand heur priorState stackHead stackTail).pathOrder x).1 ≤ (path_val priorState stackHead x adj).1:= by 
      intro x
      unfold astar_step_expand
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

    have x_still_visited : ∀ x : priorState.visited, ↑x ∈ (astar_step_expand heur priorState stackHead stackTail).visited := by 
      intro x
      unfold astar_step_expand
      grind
    
    have mother_same_order : ∀ x : priorState.visited, ∀ adj_head_x : g.Adj stackHead x,
      ((astar_step_expand heur priorState stackHead stackTail).mother ⟨x.val, x_still_visited x⟩) = (priorState.mother x) ∧ (priorState.mother x) ≠ stackHead →
      (astar_step_expand heur priorState stackHead stackTail).pathOrder x = priorState.pathOrder x := by
        intro x adj_head_x mother_same
        unfold astar_step_expand at mother_same ⊢
        grind


    have head_order_stays : ((astar_step_expand heur priorState stackHead stackTail).pathOrder stackHead).1 = (priorState.pathOrder stackHead).1 := by
      unfold astar_step_expand
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
          have mother_options := astar_mother_options heur priorState stackHead stackTail ⟨ a, a_visited⟩ (x_still_visited ⟨ a, a_visited⟩)
          cases mother_options
          · next mother_head =>
            rw [mother_head]
            rw [head_order_stays]  
            unfold astar_step_expand at mother_head ⊢
            simp_all
            grind
          · next mother_same_and_not_head =>
            obtain ⟨ mother_same, mother_not_head ⟩ := mother_same_and_not_head
            rw [mother_same]
            specialize mother_same_order ⟨a,a_visited⟩ adj_head_a ⟨ mother_same, mother_not_head⟩  
            rw [mother_same_order]
            unfold astar_step_expand at mother_same ⊢
            simp
            split_ifs <;> grind
        · unfold astar_step_expand
          simp
          grind
      · 
        by_cases a_visited : a ∈ priorState.visited
        · intro eq
          have mother_options := astar_mother_options heur priorState stackHead stackTail ⟨ a, a_visited⟩ (x_still_visited ⟨ a, a_visited⟩)
          cases mother_options
          · next mother_head =>
            rw [mother_head] at ⊢ eq
            unfold astar_step_expand at mother_head eq ⊢
            simp_all
            grind
          · next mother_same_and_not_head =>
            obtain ⟨ mother_same, mother_not_head ⟩ := mother_same_and_not_head
            rw [mother_same] at ⊢ eq
            specialize mother_same_order ⟨a,a_visited⟩ adj_head_a ⟨ mother_same, mother_not_head⟩  
            rw [mother_same_order] at ⊢ eq
            unfold astar_step_expand at mother_same eq ⊢
            simp at ⊢ eq
            split_ifs <;> grind
        · unfold astar_step_expand
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
          have h_1 : ((astar_step_expand heur priorState stackHead stackTail).pathOrder m).1 = (priorState.pathOrder m).1 := by grind
          specialize h_dec_2 m m_visited h_1
          apply h_dec_2
        · unfold WeightedDiGraph.search_invar_mother_decreasing_path_order at mother_decreasing_prior
          specialize mother_decreasing_prior ⟨a,a_visited⟩ a_not_start
          unfold FValueComp.lt at mother_decreasing_prior
          unfold Nat.instFValueCompProd at mother_decreasing_prior
          grind

      

lemma astar_expand_keeps_on_stack_or_all_neighbours_visited
    (priorState : astar_search_state  g)
    (stackHead : V)
    (stackTail : List V):
     WeightedDiGraph.search_invar_on_stack_or_all_neighbours_visited priorState
     ∧ priorState.stack = (stackHead :: stackTail)
     → WeightedDiGraph.search_invar_on_stack_or_all_neighbours_visited  
          (astar_step_expand heur priorState stackHead stackTail)
          := by
      intro ⟨ invar_holds_on_prior_state, stack_composition ⟩ 
      unfold WeightedDiGraph.search_invar_on_stack_or_all_neighbours_visited
      intro ⟨ x, x_now_on_stack⟩
      by_cases x_not_stack_head : x ≠ stackHead
      · by_cases x_was_not_in_stack_tail_: x ∈ stackTail
        · left
          unfold astar_step_expand
          simp_all
        · by_cases x_not_visited : x ∉ priorState.visited
          · left
            unfold astar_step_expand
            unfold astar_step_expand at x_now_on_stack
            simp at x_now_on_stack
            simp_all
          · simp_all -- x was visited before and is not on the stack any more
            right
            intro y x_adj_y
            unfold astar_step_expand
            simp_all
            left
            have x_invar := invar_holds_on_prior_state x
            simp_all
      · simp_all
        right
        intro y x_adj_y
        unfold astar_step_expand
        simp_all
        by_cases h : y ∈ priorState.visited
        · left; exact h
        · right; left; exact h

lemma astar_expand_keeps_start_visited
    (start : V)
    (priorState : astar_search_state  g)
    (stackHead : V)
    (stackTail : List V):
     WeightedDiGraph.search_invar_start_visited start priorState →
     WeightedDiGraph.search_invar_start_visited start (astar_step_expand heur priorState stackHead stackTail)
          := by
      intro pre_invar
      unfold astar_step_expand
      unfold WeightedDiGraph.search_invar_start_visited 
      simp_all

lemma astar_expand_visited_subset (priorState : astar_search_state  g)
    (stackHead : V)
    (stackTail : List V):
    priorState.visited ⊆ (astar_step_expand heur priorState stackHead stackTail).visited := by
    unfold astar_step_expand
    simp_all

lemma astar_expand_keeps_goal_on_stack :
   WeightedDiGraph.base_invar_carries_over_expand (state_type := astar_search_state g) (astar_step_expand heur) goal (WeightedDiGraph.search_prop_goal_on_stack (G:=g) (D:=ℕ × ℕ) goal):= by
    unfold WeightedDiGraph.base_invar_carries_over_expand
    intro s head tail ⟨ goal_prior_on_stack, head_not_goal, compose⟩ 
    change WeightedDiGraph.search_prop_goal_on_stack goal (astar_step_expand heur s head tail)
    unfold astar_step_expand
    unfold WeightedDiGraph.search_prop_goal_on_stack at ⊢ goal_prior_on_stack
    simp_all 
    cases  goal_prior_on_stack
    all_goals
      simp_all

lemma astar_expand_goal_becomes_visited_puts_it_on_stack
  (goal : V)
  : 
  WeightedDiGraph.goal_becomes_visited_puts_it_on_stack (state_type := astar_search_state g) (G:=g) (D:=ℕ×ℕ) (astar_step_expand heur) goal := by
    unfold WeightedDiGraph.goal_becomes_visited_puts_it_on_stack
    intro s head tail ⟨ a,b,c,d⟩ 
    change WeightedDiGraph.search_prop_goal_on_stack goal (astar_step_expand heur s head tail)
    have bb : goal ∈ (astar_step_expand heur s head tail).visited := b
    clear b
    unfold astar_step_expand at bb ⊢
    unfold WeightedDiGraph.search_prop_goal_on_stack
    simp_all
    cases bb
    · contradiction
    · next h => right; exact h


lemma astar_expand_keeps_base_invars:
  WeightedDiGraph.base_invar_carries_over_expand (state_type := astar_search_state g) (astar_step_expand heur) goal (WeightedDiGraph.search_invar_all_basic (G:=g) (D:=ℕ×ℕ) start) := by
  unfold WeightedDiGraph.base_invar_carries_over_expand
  unfold WeightedDiGraph.search_invar_all_basic
  intro s head tail ⟨ ⟨ i1,i2,i3,i4,i5,i6⟩ , head_not_goal, compose⟩ 
  have head_is_visited : head ∈ s.visited := by
    apply i1
    rw [compose]
    simp
  and_intros
  · apply astar_expand_keeps_stack_in_visited
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
  · apply astar_expand_keeps_mother_in_visited
    constructor
    · exact i2
    · exact head_is_visited
  · apply astar_expand_keeps_mother_is_adjacent
    exact i3
  · apply astar_expand_keeps_mother_ordered
    constructor
    · exact i2
    · constructor
      · exact head_is_visited
      · and_intros
        · exact i4
        · exact i2
  · apply astar_expand_keeps_on_stack_or_all_neighbours_visited
    constructor
    · exact i5 
    · exact compose 
  · apply astar_expand_keeps_start_visited
    exact i6


def astar (start : V) (goal : V): Option (g.Path start goal) :=
  let start_state := WeightedDiGraph.base_search_state_initial start ⟨0,0⟩
  have h : WeightedDiGraph.has_base_search_state.to_base_state (G:=g) start_state = WeightedDiGraph.base_search_state_initial start (0,0):= by simp_all only [start_state]; rfl

  WeightedDiGraph.search_exe_with_stack_step (G:=g) (start := start) (goal:=goal) (start_state:=start_state) (termination_metric := astar_termination_metric) (astar_step_expand heur) (astar_expand_metric_reduction heur) (astar_expand_keeps_base_invars heur) h 


def astar_last_state (start : V) (goal : V): WeightedDiGraph.base_search_state g (ℕ×ℕ) × Bool :=
  WeightedDiGraph.search_with_stack_step (goal:=goal) (start_state := WeightedDiGraph.base_search_state_initial start (0,0)) (astar_step_expand heur) (astar_expand_metric_reduction heur)


theorem astar_is_sound (start : V) (goal : V) :
    (Option.isSome (astar (g:=g) heur start goal) → (∃ x : (g.Path start goal), x = x)) := by
  apply WeightedDiGraph.search_with_stack_step_is_sound
  · apply astar_expand_metric_reduction
  · apply astar_expand_keeps_base_invars
  · rfl



theorem astar_is_complete (start : V) (goal : V):
    ((∃ x : (g.Path start goal), x = x) → Option.isSome (astar (g:=g) heur start goal)) := by
  apply WeightedDiGraph.search_with_stack_step_is_complete
  · apply astar_expand_metric_reduction
  · apply astar_expand_keeps_base_invars
  · rfl
  · apply astar_expand_keeps_goal_on_stack
  · apply astar_expand_goal_becomes_visited_puts_it_on_stack

/- -/
theorem astar_is_optimal (start : V) (goal : V)
    (returned_path : Option.isSome (astar (g:=g) heur start goal)):
    ((astar (g:=g) heur start goal).get returned_path).is_cheapest := by
    let final : WeightedDiGraph.base_search_state g (ℕ×ℕ) × Bool := WeightedDiGraph.search_with_stack_step (goal:=goal) (start_state := WeightedDiGraph.base_search_state_initial start (0,0)) (astar_step_expand heur) (astar_expand_metric_reduction heur)
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
      apply WeightedDiGraph.search_recurse_obtain_base_termination_property (G:=g) (D:=ℕ×ℕ) (T:=(Vector (WithTop (ℕ × ℕ)) g.nodeNum) × ℕ) goal (WeightedDiGraph.base_search_state_initial start (0,0)) (property_after_termination := WeightedDiGraph.search_prop_stack_head_is_goal (D:=ℕ×ℕ) goal ) (terminated_with := true) (search_step := WeightedDiGraph.search_stack_step (G:=g) (D:=ℕ×ℕ) (astar_step_expand (g:=g) heur)) astar_termination_metric 
      · intro s
        apply WeightedDiGraph.search_stack_step_goal_stack_head_if_terminated
      · unfold astar at returned_path
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
        apply astar_expand_keeps_base_invars

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
        apply astar_expand_keeps_base_invars

    have t_2 : WeightedDiGraph.search_invar_mother_is_adjacent start final_state := by
      unfold final_state
      unfold final
      unfold WeightedDiGraph.search_with_stack_step
      simp only []
      apply WeightedDiGraph.search_returns_with_mother_adjacent (state_type := WeightedDiGraph.base_search_state g (ℕ×ℕ)) (start_state := WeightedDiGraph.base_search_state_initial start (0,0)) (start := start)
      · rfl
      · apply WeightedDiGraph.base_invar_carries_over_stack_step
        apply astar_expand_keeps_base_invars

    have t_3 : WeightedDiGraph.search_invar_mother_decreasing_path_order start final_state := by
      unfold final_state
      unfold final
      unfold WeightedDiGraph.search_with_stack_step
      simp only []
      apply WeightedDiGraph.search_returns_with_mother_decreasing (state_type := WeightedDiGraph.base_search_state g (ℕ×ℕ)) (start_state := WeightedDiGraph.base_search_state_initial start (0,0)) (start := start)
      · rfl
      · apply WeightedDiGraph.base_invar_carries_over_stack_step
        apply astar_expand_keeps_base_invars

    sorry

end NatGraph
