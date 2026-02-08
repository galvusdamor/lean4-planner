import Graphlib.Basic


def NatGraph (V : Type) [FinEnum V] : Type := WeightedDiGraph V ℕ 



namespace NatGraph
variable {V : Type} [FinEnum V] 
variable {G : NatGraph V}


def edgeCost {u v : V} (h : G.Adj u v) : ℕ := G.Payload u v h

end NatGraph


namespace WeightedDiGraph

variable {V : Type} [FinEnum V] 
variable {G : NatGraph V}

namespace Walk

/-- `Cost` of a walk is sum of the number of all of its edges-/
def cost {u v : V} : (G.Walk u v) → ℕ
  | WeightedDiGraph.Walk.cons adj rest => (G.edgeCost adj) + cost rest
  | WeightedDiGraph.Walk.nil => 0

@[simp]
theorem append_cons_inc_cost_by_edge (w : G.Walk u v) (h : G.Adj v v') :
  (w.append (Walk.cons h Walk.nil)).cost = G.edgeCost h + w.cost := by
  unfold Walk.append
  split
  · repeat unfold Walk.cost
    simp_all
  · unfold Walk.cost 
    conv =>
      right
      rw [add_comm]
      rw [add_assoc]
      right
      rw [add_comm]
    apply Nat.add_left_cancel_iff.mpr
    apply append_cons_inc_cost_by_edge


@[simp]
theorem concat_inc_cost_by_edge (p : G.Walk u v) (h : G.Adj v w) :
      (p.concat h).cost = G.edgeCost h + p.cost := by
  unfold Walk.concat
  apply append_cons_inc_cost_by_edge

@[simp]
theorem cost_nil_zero {u : V} : (Walk.nil : G.Walk u u).cost = 0 := by unfold cost ; rfl 

theorem contains_subwalk_cost {u v w : V} (p : G.Walk u v) (w_in_walk : w ∈ p.support) (w_ne_v : w ≠ v):
    ∃ p' : G.Walk u w, p'.cost ≤ p.cost ∧ p'.support <+: p.support := by
    by_cases u_eq_w : u = w
    · let w' : G.Walk u u := Walk.nil
      use u_eq_w ▸ w'
      subst u_eq_w
      rw [cost_nil_zero]
      simp_all
      unfold support
      grind
    · cases p
      · unfold support at w_in_walk
        simp_all -- contradictory
      · next a b c =>
        unfold support at w_in_walk
        simp_all
        cases w_in_walk
        · grind
        · next w_in_c =>
          obtain ⟨p',length_le⟩ := contains_subwalk_cost c w_in_c w_ne_v
          use (Walk.cons b p')
          unfold cost
          constructor
          · grind
          · unfold support
            grind 



end Walk

namespace Path

def cost {u v : V} (p : G.Path u v) : ℕ := Walk.cost p.val


@[simp]
theorem cost_same {u v : V} (p : G.Path u v):
    p.cost = p.val.cost := by unfold cost ; rfl

@[simp]
theorem cost_nil_zero {u : V} : (G.nil_path u).cost = 0 := by
  unfold cost nil_path
  unfold Walk.cost
  simp_all

@[simp]
theorem cost_nil_walk_zero {u : V} : (G.nil_path u).val.length  = 0 := by
  unfold Walk.length nil_path
  simp_all


@[simp]
theorem concat_inc_cost_by_edge (p : G.Path u v) (h : G.Adj v w) (proof_w_not_in_support : w ∉ p.support) :
      (p.concat h proof_w_not_in_support).cost = G.edgeCost h + p.cost := by
  apply Walk.concat_inc_cost_by_edge 



def is_cheapest {u v : V} (p : G.Path u v) : Prop :=
  ∀ p' : G.Path u v, p.cost ≤ p'.cost


theorem contains_subpath_cost {u v w : V} (p : G.Path u v) (w_in_path : w ∈ p.support) (w_ne_v : w ≠ v):
    ∃ p' : G.Path u w, p'.cost ≤ p.cost := by
    obtain ⟨w',len,supp⟩ := p.val.contains_subwalk_cost w_in_path w_ne_v 
    have p_nodup : w'.support.Nodup := by
      apply List.Nodup.sublist (l₂ := p.support)
      · apply List.IsPrefix.sublist
        exact supp
      · exact p.prop
    use ⟨ w', p_nodup⟩
    unfold cost
    apply len

end Path


end WeightedDiGraph

namespace NatGraph
variable {V : Type} [FinEnum V] 
variable {G : NatGraph V}

def cost_is (u v : V) (dist: ℕ) : Prop :=
  (∃ p : G.Path u v, p.cost = dist ∧ p.is_cheapest)

def cost_ge (u v : V) (dist: ℕ) : Prop :=
  ∀ p : G.Path u v, p.cost ≥ dist

def cost_gt (u v : V) (dist: ℕ) : Prop :=
  ∀ p : G.Path u v, p.cost > dist

def cost_lt (u v : V) (dist: ℕ) : Prop :=
  ∃ p : G.Path u v, p.cost < dist

lemma cost_ge_lt (u v : V) (d1 d2: ℕ) :
    G.cost_ge u v d1 ∧ d2 ≤ d1 → G.cost_ge u v d2 := by
    unfold NatGraph.cost_ge
    simp_all
    intro ge_d1 d2_le_d1 p p_nodup
    apply le_trans
    · exact d2_le_d1
    · exact ge_d1 p p_nodup


end NatGraph
