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

set_option trace.split.failure true
--set_option diagnostics true

-- def local global variable for a graph
variable {V : Type} [FinEnum V] [DecidableEq V]
variable {g : NatGraph V}


namespace NatGraph
-----------------------------------------------------------------------
------ BFS implementation and proof ------

def dijkstra_step_expand[FinEnum V] [DecidableEq V]
    (g: NatGraph V)
    (priorState : base_search_state g)
    (stackHead : V)
    (stackTail : List V):
    (base_search_state g) :=
      -- all neighbours that either are *not visited yet* or are not on stack (to avoid dupliactes) and have shorter path via stackHead
      let newly_visited : Finset V := (Finset.univ).filterMap
        (λ v => if h : @decide (g.Adj stackHead v) (g.instDecAdj stackHead v) then
            let adj : g.Adj stackHead v := by simp_all only [decide_eq_true_eq] 
            if v ∉ priorState.visited ∨
              (v ∈ priorState.visited ∧ v ∉ stackTail ∧ priorState.pathOrder v > priorState.pathOrder stackHead + g.edgeCost adj)    then some v else none else none)
        (by intro a a' b a_1 a_2; simp_all) -- filter neighbors to expand the visited list
      
      let vList : List V := (FinEnum.toList (Finset.univ : Finset V))
      let newly_visited_list : List V := vList.filterMap (λ v => if v ∈ newly_visited then some v else none)
      let new_visited : Finset V := priorState.visited ∪ newly_visited


      let new_order : V → Nat := fun v  =>
        if h : @decide (g.Adj stackHead v) (g.instDecAdj stackHead v) then
          let adj : g.Adj stackHead v := by simp_all only [decide_eq_true_eq] 
          if (v ∉ priorState.visited) then   priorState.pathOrder stackHead + g.edgeCost adj
          else min (priorState.pathOrder v) (priorState.pathOrder stackHead + g.edgeCost adj)
        else priorState.pathOrder v


      let new_mother : new_visited → V := fun ⟨v, hv⟩  =>
        if h : @decide (g.Adj stackHead v) (g.instDecAdj stackHead v) then
          let adj : g.Adj stackHead v := by simp_all only [decide_eq_true_eq] 
          if hh : (v ∉ priorState.visited) then stackHead 
          else
            if (priorState.pathOrder v) > (priorState.pathOrder stackHead + g.edgeCost adj) then
              stackHead
            else
              priorState.mother ⟨v, by simp_all⟩
        else priorState.mother ⟨v, by grind⟩


     let new_stack : List V := (stackTail ++ newly_visited_list).mergeSort (fun a b =>
        new_order a ≤ new_order b) 
       
     base_search_state.mk new_visited new_order new_mother new_stack


end NatGraph
