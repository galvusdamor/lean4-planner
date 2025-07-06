import Aesop

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Basic

abbrev StripsState (nvar : Nat) := Finset (Fin nvar)

structure StripsAction (nvar : Nat) where
  pre : Finset (Fin nvar)
  add : Finset (Fin nvar)
  del : Finset (Fin nvar)
  no_pre_added : pre ∩ add = ∅
  no_del_added : add ∩ del = ∅

abbrev StripsActionSequence (nvar : Nat) (len : Nat) := Vector (StripsAction nvar) len

structure StripsDomain (nvar : Nat) (nact : Nat) where
  actions : Vector (StripsAction nvar) nact

structure StripsProblem (nvar : Nat) (nact : Nat) where
  domain : StripsDomain nvar nact
  init : StripsState nvar
  goal : StripsState nvar


variable {nvar : Nat}
variable {nact : Nat}


def stripsApplicable (a: StripsAction nvar) (s : StripsState nvar) : Bool := a.pre ⊆ s

def stripsApply (a: StripsAction nvar) (s : StripsState nvar) : (StripsState nvar) := (s \ a.del) ∪ a.add

lemma two_applications_of_same_action_dont_change_state {a : StripsAction nvar} {s : StripsState nvar} :
    stripsApply a s = stripsApply a (stripsApply a s) := by
      unfold stripsApply
      ext a_1
      simp_all only [Finset.mem_union, Finset.mem_sdiff]
      apply Iff.intro
      · intro a_2
        simp_all only [true_and]
        cases a_2 with
        | inl h => simp_all only [not_false_eq_true, true_or]
        | inr h_1 => simp_all only [or_true]
      · intro a_2
        cases a_2 with
        | inl h =>
          simp_all only [not_false_eq_true, and_true]
          obtain ⟨left, right⟩ := h
          simp_all only [not_false_eq_true, and_true]
        | inr h_1 => simp_all only [or_true]

def stripsIsDeleteRelaxed (a: StripsAction nvar) := a.del = ∅

lemma delete_relaxed_larger_state_is_better {a : StripsAction nvar} {s : StripsState nvar} {s' : StripsState nvar} : s ⊆ s' → (stripsApplicable a s) → stripsApplicable a s' := by
  unfold stripsApplicable
  simp
  intro s_less_s'
  intro a_appli
  apply Finset.Subset.trans
  exact a_appli
  exact s_less_s'



-- either returns none if not applicable or the state after the last action
def stripsApplyActionSequence {l : Nat} (as : StripsActionSequence nvar l) (s : StripsState nvar) : Option (StripsState nvar) := 
  if empty: l == 0 then (some s)
  else 
    let f : 0 < l := by
      apply Nat.zero_lt_of_ne_zero
      simp at empty
      exact empty
    let firstAction := as.get ⟨0, f⟩
    let otherActions := as.tail
    if !(stripsApplicable firstAction s) then none
    else stripsApplyActionSequence otherActions (stripsApply firstAction s)


def stripsActionSequenceApplicable {l : Nat} (as : StripsActionSequence nvar l) (s : StripsState nvar) : Bool := stripsApplyActionSequence as s != none 

def stripsIsActionSequencePlan {l : Nat} (problem : StripsProblem nvar nact) (as : StripsActionSequence nvar l) : Bool :=
  let result := stripsApplyActionSequence as problem.init
  match result with
   | none => False
   | some s => problem.goal ⊆ s













