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



def is_cheapest {u v : V} (p : G.Path u v) : Prop :=
  ∀ p' : G.Path u v, p.cost ≤ p'.cost



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
