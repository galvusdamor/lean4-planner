import Graphlib.Basic


def NatGraph (V : Type) [FinEnum V] : Type := WeightedDiGraph V ℕ 



namespace NatGraph
variable {V : Type} [FinEnum V] 
variable {G : NatGraph V}


def edgeCost {u v : V} (h : G.Adj u v) : ℕ := G.Payload u v h


namespace Walk

/-- `Cost` of a walk is sum of the number of all of its edges-/
def cost {u v : V} : (G.Walk u v) → ℕ
  | WeightedDiGraph.Walk.cons adj rest => (G.edgeCost adj) + cost rest
  | WeightedDiGraph.Walk.nil => 0

end Walk

namespace Path

def cost {u v : V} (p : G.Path u v) : ℕ := Walk.cost p.val

end Path

end NatGraph
