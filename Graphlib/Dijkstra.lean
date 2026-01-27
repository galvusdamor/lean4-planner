import Mathlib.Data.Bool.AllAny
import Mathlib.Data.FinEnum
import Mathlib.Data.Finset.Empty
import Mathlib.Data.List.MinMax
import Mathlib.Order.Basic
import Mathlib.Data.Multiset.DershowitzManna
import Mathlib.Data.Finsupp.WellFounded
import Mathlib.Data.List.ToFinsupp
import Mathlib.Algebra.Group.WithOne.Defs

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


instance : IsTrichotomous ℕ Nat.lt where
 trichotomous (a b : ℕ) : Nat.lt a b ∨ a = b ∨ Nat.lt b a := by
   simp
   by_cases h : a < b
   · left ; exact h
   by_cases hh : b < a
   · right ; right ; exact hh
   right ; left ; omega

def Fin.lt (n : ℕ) (a b : Fin n) : Prop := a.val < b.val

instance {n : ℕ} : IsTrichotomous (Fin n) (Fin.lt n) where
 trichotomous (a b : Fin n) : Nat.lt a b ∨ a = b ∨ Nat.lt b a := by
   simp
   by_cases h : a < b
   · left ; exact h
   by_cases hh : b < a
   · right ; right ; exact hh
   right ; left ; omega




def zero_wf_rel {α : Type} (rel_a : α → α → Prop) (a b : WithZero α) : Prop := 
  match (a,b) with
  | (.none, .none) => False
  | (.none, .some _) => True
  | (.some _ ,.none) => False
  | (.some a', .some b') => rel_a a' b'


def nonZero {α : Type} [Zero α] (l : List α) := ∀ a ∈ l, a ≠ Zero.zero

def ListNonZero (α : Type) (n : ℕ) [Zero α] := {l : List α // nonZero l ∧ l.length = n}

def List.LexNonZero {α : Type} [Zero α] (n : ℕ) (r : α → α → Prop) (a b : ListNonZero α n):= List.Lex r a.val b.val



def Vector.Lex (n : ℕ) (r : α → α → Prop) (as : Vector α n) (bs : Vector α n) : Prop :=
  List.Lex r as.toArray.toList bs.toArray.toList 



-- not needed ... (h : n = l.length)
private def toFinsuppFin {M : Type} [Zero M] (l : List M) (n : ℕ) [DecidablePred fun i => l.getD (↑i) 0 ≠ 0] : (Fin n) →₀ M where
  toFun i := l.getD i 0
  support := {i : Fin n | l.getD i 0 ≠ 0}
  mem_support_toFun n := by
    simp only [Ne, Finset.mem_filter, and_iff_right_iff_imp]
    contrapose
    intro n_ne_in_Fin
    apply List.getD_eq_default
    grind


noncomputable instance {α : Type} (l : List (WithZero α)) (a : ℕ): Decidable (l.getD a 0 ≠ 0) := by
   simp
   by_cases h : ¬l[a]?.getD 0 = 0
   · use .isTrue h 
   · use .isFalse (by simp [h])

-- not needed (h : n = l.length)
private noncomputable def list_to_finsupp {α : Type} (n : ℕ) (l : List (WithZero α)) : Finsupp (Fin n) (WithZero α) := toFinsuppFin l n


@[simp, norm_cast]
theorem List.toFinsuppFin_apply {M : Type} [Zero M] (l : List M) [DecidablePred fun i => l.getD (↑i) 0 ≠ 0] (i : Fin l.length) : (toFinsuppFin l l.length: Fin l.length → M) i = l.getD i 0 :=
  rfl

@[simp]
theorem List.toFinsuppFin_cons {n : ℕ} {M : Type} [Zero M] (a : M) (l : List M) [DecidablePred fun i => (a :: l).getD (↑i) 0 ≠ 0] [DecidablePred fun i => l.getD (↑i) 0 ≠ 0] (i : Fin (n-1)) (h : i+1 < n):
    (toFinsuppFin (a :: l) n) (⟨i+1, h⟩) = (toFinsuppFin l (n-1)) i := rfl 


@[simp]
theorem List.toFinsuppFin_head {n : ℕ} {M : Type} [Zero M] (a : M) (l : List M) [DecidablePred fun i => (a :: l).getD (↑i) 0 ≠ 0] (h : 0 < n):
    (toFinsuppFin (a :: l) n) (⟨0, h⟩) = a := rfl 


private noncomputable def non_zero_list_to_finsupp {α : Type} (n : ℕ) (l : ListNonZero (WithZero α) n) : Finsupp (Fin n) (WithZero α) := list_to_finsupp n l.val --l.prop.2.symm


theorem List.getElem?_after_length {α : Type u} (l : List α) (i : ℕ) (h : l.length ≤ i) :
  l[i]? = none := by
    induction l
    case nil => grind
    case cons head tail ih =>
      rw [List.getElem?_cons]
      grind

private lemma List.lex_and_nonZero_then_Finsupp_lex {α : Type} (n : ℕ) (wf_a : WellFoundedRelation α) (l1 l2 : List (WithZero α)) (l1z : nonZero l1) (l2z : nonZero l2)
(h1 : n = l1.length) (h2 : n = l2.length):
List.Lex (zero_wf_rel wf_a.rel) l1 l2 →
  Finsupp.Lex (Fin.lt n) (zero_wf_rel wf_a.rel) (list_to_finsupp n l1) (list_to_finsupp n l2) := by
    intro lex
    unfold Finsupp.Lex Pi.Lex
    cases lex
    case nil a l =>
      use ⟨0, by grind⟩ 
      and_intros
      · intro j j_lt_0
        unfold list_to_finsupp 
        simp_all
      · unfold zero_wf_rel list_to_finsupp
        simp
        split
        · rename_i heq
          simp_all only [Prod.mk.injEq]
          obtain ⟨left, right⟩ := heq
          unfold nonZero at l2z
          simp_all
        · trivial
        · simp_all
        · simp_all
    case rel a_1 l_1 a_2 l_2 r =>
      use ⟨ 0, by grind ⟩
      and_intros
      · intro j j_lt_0
        unfold Fin.lt at j_lt_0
        simp_all
      · unfold zero_wf_rel list_to_finsupp
        simp
        split
        rotate_left
        · trivial
        all_goals
          rename_i heq
          simp [Prod.mk.injEq] at heq
          obtain ⟨left, right⟩ := heq
          subst left right
          exact r 
    case cons a l_1 l_2 h =>
      have r : Finsupp.Lex (Fin.lt (n-1)) (zero_wf_rel wf_a.rel) (list_to_finsupp (n-1) l_1) (list_to_finsupp (n-1) l_2) := by
        apply List.lex_and_nonZero_then_Finsupp_lex
        · unfold nonZero at l1z ⊢
          simp_all
        · unfold nonZero at l2z ⊢
          simp_all
        · grind
        · grind 
        · exact h
      unfold Finsupp.Lex Pi.Lex at r
      obtain ⟨i, ⟨c_1,c_2 ⟩ ⟩ := r
      use ⟨i+1, by grind⟩
      and_intros
      · intro j j_lt_i_succ
        by_cases j_gt_zero : j > ⟨ 0, by grind ⟩
        · let k : Fin (n-1) := ⟨ j-1, by grind ⟩
          have j_min_1_lt_i : Fin.lt (n-1) k i := by
            unfold Fin.lt at j_lt_i_succ ⊢
            unfold k
            simp_all
            omega
          specialize c_1 k j_min_1_lt_i
          unfold list_to_finsupp at c_1 ⊢ 
          let k_p_1 : Fin (n):= ⟨ k+1, by grind ⟩
          have j_k_succ : j = k_p_1 := by 
            unfold k_p_1 k ; grind
          rw [j_k_succ]
          unfold k_p_1
          simp_all
        · unfold list_to_finsupp
          have j_eq_zero : j = ⟨0, by grind ⟩ := by grind
          simp_all
      · whnf
        split
        rotate_left
        · trivial
        all_goals
          rename_i heq
          simp [Prod.mk.injEq] at heq
          obtain ⟨left,right⟩ := heq
          unfold list_to_finsupp at left right c_2
          unfold zero_wf_rel at c_2
          simp_all



private lemma List.Finsupplex_and_nonZero_then_lex {α : Type} (n : ℕ) (wf_a : WellFoundedRelation α) (l1 l2 : List (WithZero α)) (l1z : nonZero l1) (l2z : nonZero l2)
(len1 : n = l1.length) (len2 : n = l2.length):
  Finsupp.Lex (Fin.lt n) (zero_wf_rel wf_a.rel) (list_to_finsupp n l1) (list_to_finsupp n l2) → List.Lex (zero_wf_rel wf_a.rel) l1 l2:= by
    intro lex
    unfold Finsupp.Lex Pi.Lex at lex
    obtain ⟨i, ⟨c_1, c_2⟩⟩ := lex
    by_cases n_eq_zero : n = 0
    · subst n_eq_zero
      have h := i.prop
      grind
    by_cases i_eq_zero : i = ⟨ 0, by grind ⟩
    · subst i_eq_zero
      unfold zero_wf_rel list_to_finsupp at c_2
      simp_all
      cases l1 <;> cases l2
      · simp_all
      · simp_all
      · simp_all
      · simp_all
        rename_i h1 t1 h2 t2
        split at c_2
        · simp_all
        · rename_i heq
          simp [Prod.mk.injEq] at heq
          obtain ⟨left,right⟩ := heq
          unfold nonZero at l1z
          simp_all
          have prob := l1z.1
          clear left right l1z l2z
          exfalso
          apply prob
          clear prob
          rfl
        · simp_all
        · rename_i a b heq
          simp [Prod.mk.injEq] at heq
          obtain ⟨left,right⟩ := heq
          subst left right
          apply List.Lex.rel
          unfold zero_wf_rel
          simp_all
    · have h : Nat.lt 0 i := by simp ; grind 
      cases l1 <;> cases l2
      · specialize c_1 ⟨0,by grind⟩ h
        unfold list_to_finsupp at c_2
        simp_all
      · specialize c_1 ⟨0,by grind⟩ h
        unfold list_to_finsupp at c_2
        simp_all
      · rename_i head tail
        specialize c_1 ⟨0,by grind⟩ h
        clear c_2
        unfold list_to_finsupp at c_1
        simp_all
      · rename_i h1 t1 h2 t2 
        have h_eq : h1 = h2 := by
          specialize c_1 ⟨0,by grind⟩ h
          unfold list_to_finsupp at c_1
          simp_all
        subst h_eq
        apply List.Lex.cons
        apply List.Finsupplex_and_nonZero_then_lex (n-1)
        · unfold nonZero at l1z ⊢
          simp_all
        · unfold nonZero at l2z ⊢
          simp_all
        · grind
        · grind
        · unfold Finsupp.Lex Pi.Lex
          use ⟨i-1, by grind ⟩
          and_intros
          · intro j j_lt_i_min_one
            let k : Fin n := ⟨ j+1, by grind ⟩
            have j_succ_lt_i : Fin.lt n k i := by unfold Fin.lt at ⊢ j_lt_i_min_one ; simp_all ; grind 
            specialize c_1 k j_succ_lt_i
            unfold k at c_1
            unfold list_to_finsupp at c_1 ⊢
            simp_all
          · let k : Fin (n-1) := ⟨ i-1, by grind ⟩
            have i_eq : i = ⟨k+1, by grind ⟩ := by unfold k ; grind
            unfold list_to_finsupp at c_2 ⊢
            simp_all

private lemma List.lexNonZero_then_Finsupp_lex {α : Type} (n : ℕ) (wf_a : WellFoundedRelation α) (l1 l2 : ListNonZero (WithZero α) n):
List.LexNonZero n (zero_wf_rel wf_a.rel) l1 l2 →
  Finsupp.Lex (Fin.lt n) (zero_wf_rel wf_a.rel) (non_zero_list_to_finsupp n l1) (non_zero_list_to_finsupp n l2) := by
    unfold List.LexNonZero non_zero_list_to_finsupp
    apply List.lex_and_nonZero_then_Finsupp_lex
    · exact l1.prop.1
    · exact l2.prop.1
    · grind
    · grind

private lemma List.Finsupp_lex_then_lexNonZero {α : Type} (n : ℕ) (wf_a : WellFoundedRelation α) (l1 l2 : ListNonZero (WithZero α) n):
  Finsupp.Lex (Fin.lt n) (zero_wf_rel wf_a.rel) (non_zero_list_to_finsupp n l1) (non_zero_list_to_finsupp n l2) → 
List.LexNonZero n (zero_wf_rel wf_a.rel) l1 l2  := by
    unfold List.LexNonZero non_zero_list_to_finsupp
    apply List.Finsupplex_and_nonZero_then_lex
    · exact l1.prop.1
    · exact l2.prop.1
    · grind
    · grind

theorem WithZero.Acc.none {α : Type} (wf_a : WellFoundedRelation α) : Acc (zero_wf_rel (WellFoundedRelation.rel : α → α → Prop)) .none := by 
    apply Acc.intro
    intro y rel
    by_contra
    unfold zero_wf_rel at rel
    clear this
    split at rel <;> simp_all

theorem WithZero.Acc.some {α : Type} (wf_a : WellFoundedRelation α) (a : α) : Acc (zero_wf_rel WellFoundedRelation.rel) (.some a) := by 
  apply Acc.intro
  intro y rel
  unfold zero_wf_rel at rel
  split at rel
  · simp_all
  · simp_all; apply WithZero.Acc.none
  · simp_all
  · rename_i x xx xxx compose  
    simp_all
    obtain ⟨l,r⟩ := compose
    subst l
    apply WithZero.Acc.some
termination_by wf_a.wf.wrap a
decreasing_by
  rename_i a_1 rel_1 a' b' h heq
  subst l
  simp_all only [WellFounded.val_wrap]
  have h : a = b' := by grind
  rw [h]
  exact rel


theorem WithZero.Acc {α : Type} (wf_a : WellFoundedRelation α) (a : WithZero α) : Acc (zero_wf_rel WellFoundedRelation.rel) a := by 
  cases a
  · apply WithZero.Acc.none 
  · apply Acc.intro
    intro y rel
    unfold zero_wf_rel at rel
    split at rel
    · simp_all
    · simp_all; apply WithZero.Acc.none
    · simp_all
    · simp_all; apply WithZero.Acc.some


theorem wf_with_zero {α : Type} (wf_a : WellFoundedRelation α) : WellFounded (zero_wf_rel wf_a.rel) := by 
  apply WellFounded.intro
  intro a
  apply WithZero.Acc


theorem Fin.gt.is_wf {n : ℕ} : WellFounded (Function.swap (Fin.lt n)) := by
  apply WellFounded.intro
  apply WellFoundedGT.apply

theorem wf_list_with_zero {α : Type} (n : ℕ) (wf_a : WellFoundedRelation α) : WellFounded (List.LexNonZero n (zero_wf_rel wf_a.rel)) := by
  have finsupp_lex_wf : WellFounded (Finsupp.Lex (Fin.lt n) (zero_wf_rel wf_a.rel)) := by
    apply Finsupp.Lex.wellFounded'
    · intro n
      unfold zero_wf_rel
      split
      · grind
      · rename_i heq 
        simp [Prod.mk.injEq] at heq
      · grind
      · rename_i heq 
        simp [Prod.mk.injEq] at heq
    · apply wf_with_zero
    · exact Fin.gt.is_wf 

  have h := InvImage.wf (non_zero_list_to_finsupp n) (finsupp_lex_wf)
  convert h
  unfold InvImage
  ext l1 l2
  constructor
  · apply List.lexNonZero_then_Finsupp_lex
  · apply List.Finsupp_lex_then_lexNonZero


private def zero_remove {α : Type} {n : ℕ}(l : Vector α n) : ListNonZero (WithZero α) n := 
  let l_0 : List (WithZero α) := l.toArray.toList.map (.some ·)
  have p_0 : nonZero l_0 := by
    unfold nonZero l_0
    intro a in_map
    apply List.mem_map.mp at in_map
    obtain ⟨ _, ⟨ _, p ⟩ ⟩ := in_map
    rw [← p]
    unfold Zero.zero
    unfold WithZero.instZero
    simp
  ⟨l_0, p_0, by grind⟩ 


private lemma Vector.lex_toList_non_zero_lex {α : Type} (n : ℕ) (wf_a : WellFoundedRelation α) (l1 l2 : List α)
  (lex : List.Lex WellFoundedRelation.rel l1 l2)
  (p1 : nonZero ((List.map (fun x => some x) l1) : List (WithZero α)) ∧ (List.map (fun x => some x) l1).length = n)
  (p2 : nonZero ((List.map (fun x => some x) l2) : List (WithZero α)) ∧ (List.map (fun x => some x) l2).length = n)
  :
  List.LexNonZero n (zero_wf_rel wf_a.rel) ⟨List.map (fun x => some x) l1, p1⟩ ⟨List.map (fun x => some x) l2, p2⟩ := by
    cases l1 <;> cases l2
    · cases lex
    · cases lex
      unfold List.LexNonZero
      apply List.Lex.nil
    · cases lex
    · cases lex
      · unfold List.LexNonZero
        apply List.Lex.rel
        unfold zero_wf_rel
        grind
      · unfold List.LexNonZero
        apply List.Lex.cons
        apply Vector.lex_toList_non_zero_lex (n := n-1)
        · grind
        · and_intros
          · obtain ⟨r,l⟩ := p1
            unfold nonZero at r ⊢
            grind
          · grind
        · and_intros
          · obtain ⟨r,l⟩ := p2
            unfold nonZero at r ⊢
            grind
          · grind


private lemma List.non_zero_lex_to_vector_lex {α : Type} (n : ℕ) (wf_a : WellFoundedRelation α) (l1 l2 : List α)
  (p1 : nonZero ((List.map (fun x => some x) l1) : List (WithZero α)) ∧ (List.map (fun x => some x) l1).length = n)
  (p2 : nonZero ((List.map (fun x => some x) l2) : List (WithZero α)) ∧ (List.map (fun x => some x) l2).length = n)
  (lex : List.LexNonZero n (zero_wf_rel wf_a.rel) ⟨List.map (fun x => some x) l1, p1⟩ ⟨List.map (fun x => some x) l2, p2⟩)
  :
  List.Lex WellFoundedRelation.rel l1 l2 := by
    unfold LexNonZero at lex
    cases l1 <;> cases l2
    · simp_all
    · simp_all
    · simp_all
    · simp_all
      cases lex
      case rel h =>
        apply List.Lex.rel
        unfold zero_wf_rel at h
        grind
      case cons h =>
        apply List.Lex.cons
        apply List.non_zero_lex_to_vector_lex
        · unfold LexNonZero
          apply h
        · use n-1
        · and_intros
          · obtain ⟨r,l⟩ := p1
            unfold nonZero at r ⊢
            grind
          · grind

        · and_intros
          · obtain ⟨r,l⟩ := p2
            unfold nonZero at r ⊢
            grind
          · grind


theorem wf_list {α : Type} (n : ℕ) (wf_a : WellFoundedRelation α) : WellFounded (Vector.Lex n wf_a.rel) := by
  have list_wf : WellFounded (List.LexNonZero n (zero_wf_rel wf_a.rel)) := wf_list_with_zero n wf_a

  have h := InvImage.wf (zero_remove) list_wf
  convert h
  unfold InvImage
  ext l1 l2
  constructor
  · intro lex
    unfold Vector.Lex at lex
    unfold zero_remove
    simp
    apply Vector.lex_toList_non_zero_lex
    exact lex 
  · intro lex
    unfold Vector.Lex at lex
    unfold zero_remove at lex
    simp_all
    apply List.non_zero_lex_to_vector_lex
    exact lex
    


def withTop.lex {α : Type} (rel_a : α → α → Prop)  (a b : WithTop α) :=
  match (a,b) with
  | (.none, .none) => False
  | (.none, .some _) => False
  | (.some _ ,.none) => True
  | (.some a', .some b') => rel_a a' b'

theorem with_top_acc.some {α : Type} (wf_a : WellFoundedRelation α) (a : α):
   Acc (withTop.lex wf_a.rel) (.some a) := by
   apply Acc.intro
   intro y rel
   unfold withTop.lex at rel
   split at rel
   · simp_all
   · simp_all
   · rename_i x val heq
     simp [Prod.mk.injEq] at heq
     obtain ⟨r,l⟩ := heq
     unfold WithTop WithTop.some at l
     simp_all 
   · rename_i x a' b' heq
     simp [Prod.mk.injEq] at heq
     obtain ⟨r,l⟩ := heq
     subst r
     have h := wf_a.wf
     apply with_top_acc.some
termination_by wf_a.wf.wrap a
decreasing_by
  · rename_i val h' a' a'' heq h''
    subst r
    simp_all only [WellFounded.val_wrap]
    unfold withTop.lex at h'
    split at h'
    · simp_all
    · simp_all
    · simp_all
    · rename_i x a''' b' heq
      simp [Prod.mk.injEq] at heq
      obtain ⟨r,l⟩ := heq
      have h1 : a' = a''' := by grind
      have h2 : a'' = b' := by grind
      have h3 : a'' = a := by
        rename_i l'
        unfold WithTop WithTop.some at l'
        grind
      subst h1 h2 h3
      exact h'


theorem with_top_acc.none {α : Type} (wf_a : WellFoundedRelation α):
   Acc (withTop.lex wf_a.rel) .none := by
   apply Acc.intro
   intro y rel
   unfold withTop.lex at rel
   split at rel 
   · grind
   · grind
   · rename_i heq
     simp [Prod.mk.injEq] at heq
     subst heq
     apply with_top_acc.some
   · grind

theorem wf_with_top {α : Type} (wf_a : WellFoundedRelation α) : WellFounded (withTop.lex wf_a.rel) := by 
  apply WellFounded.intro
  intro a
  cases a
  · apply with_top_acc.none 
  · apply with_top_acc.some 

instance : IsWellFounded ℕ Nat.lt where
  wf := Nat.lt_wfRel.wf

instance : WellFoundedRelation (WithTop (ℕ × ℕ)):=
  WellFoundedRelation.mk (withTop.lex (Prod.Lex Nat.lt Nat.lt))
    (wf_with_top (WellFoundedRelation.mk (Prod.Lex Nat.lt Nat.lt)
      (Prod.instWellFoundedRelation (α := ℕ) (β := ℕ)).wf))


instance (n : ℕ) : WellFoundedRelation (Vector (WithTop (ℕ × ℕ)) n) :=
  WellFoundedRelation.mk (Vector.Lex n (withTop.lex (Prod.Lex Nat.lt Nat.lt)))
    (wf_list n inferInstance)


instance (n : ℕ) : WellFoundedRelation ((Vector (WithTop (ℕ × ℕ)) n) × ℕ) :=
  WellFoundedRelation.mk (Prod.Lex (Vector.Lex n (withTop.lex (Prod.Lex Nat.lt Nat.lt))) Nat.lt)
      (Prod.instWellFoundedRelation (α := (Vector (WithTop (ℕ × ℕ)) n)) (β := ℕ)).wf


def dijkstra_termination_metric 
    (s : dijkstra_search_state g): (List (WithTop (ℕ × ℕ))) × ℕ :=
    ((FinEnum.toList (Finset.univ : Finset V)).map  (fun v =>
      if v ∈ s.visited then
        WithTop.some (s.pathOrder v)
      else ⊤
    ) , s.stack.length)

--set_option trace.Meta.synthInstance true

lemma dijkstra_expand_metric_reduction : WeightedDiGraph.termination_proof_for_expand (G:=g) (state_type := dijkstra_search_state g) (D:=ℕ ×ℕ) (dijkstra_step_expand) goal dijkstra_termination_metric := by
    unfold WeightedDiGraph.termination_proof_for_expand
    intro state head tail ⟨head_ne_goal,compose⟩
    unfold WellFoundedRelation.rel
    unfold Prod.instWellFoundedRelation
    apply Prod.lex_iff.mpr
    apply (Classical.or_iff_not_imp_left).mpr
    intro not_decreasing
    and_intros
    · unfold WellFoundedRelation.rel dijkstra_termination_metric at not_decreasing
      simp_all
      sorry
    · sorry







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
