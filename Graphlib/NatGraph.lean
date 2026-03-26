import Graphlib.Basic
import Graphlib.FinEnum


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
theorem append_cost (w : G.Walk u v) (w' : G.Walk v v') :
  (w.append w').cost = w.cost + w'.cost := by
  induction w with
  | nil => simp [Walk.append, Walk.cost]
  | cons h p ih =>
    simp [Walk.append, Walk.cost, ih, Nat.add_assoc]

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
          · simp_all



@[simp]
theorem dropUntilMakesCheaper (p : G.Walk u v) (f : V) (h : f ∈ p.support):
  (p.dropUntil f h).cost ≤ p.cost := by
  induction p with
  | nil =>
    unfold cost dropUntil
    split
    · next nil_eq_cons =>
      simp at nil_eq_cons
      exfalso
      apply walk_trans (V:=V)
      apply nil_eq_cons
    · simp
  | cons _ p' ih =>
    unfold dropUntil
    split
    · rename_i h_2
      subst h_2
      simp_all only [le_refl]
    · trans
      · apply ih
      · simp!


theorem cost_bypass_le (p : G.Walk u v) : p.bypass.cost ≤ p.cost:= by
  induction p with
  | nil =>
    unfold bypass cost
    rfl
  | cons f_adj_t p' ih =>
    unfold bypass
    simp_all
    split
    · conv =>
        right
        unfold cost
      trans
      · apply dropUntilMakesCheaper
      · grind
    · unfold cost
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
theorem cost_empty_zero {u : V} (p : G.Path u u) : p.cost = 0 := by
  unfold cost
  unfold Walk.cost
  cases compose : p.val
  · simp
  case cons w h p' =>
    have u_in_p' : u ∈ p'.support := by simp
    have p_prop := p.prop
    unfold List.Nodup at p_prop
    rw [compose] at p_prop
    apply List.pairwise_cons.mp at p_prop
    grind

@[simp]
theorem concat_inc_cost_by_edge (p : G.Path u v) (h : G.Adj v w) (proof_w_not_in_support : w ∉ p.support) :
      (p.concat h proof_w_not_in_support).cost = G.edgeCost h + p.cost := by
  apply Walk.concat_inc_cost_by_edge



def is_cheapest {u v : V} (p : G.Path u v) : Prop :=
  ∀ p' : G.Path u v, p.cost ≤ p'.cost


theorem contains_subpath_cost {u v w : V} (p : G.Path u v) (w_in_path : w ∈ p.support) (w_ne_v : w ≠ v):
    ∃ p' : G.Path u w, p'.cost ≤ p.cost ∧ p'.support <+: p.support := by
    obtain ⟨w',len,supp⟩ := p.val.contains_subwalk_cost w_in_path w_ne_v
    have p_nodup : w'.support.Nodup := by
      apply List.Nodup.sublist (l₂ := p.support)
      · apply List.IsPrefix.sublist
        exact supp
      · exact p.prop
    use ⟨ w', p_nodup⟩
    constructor
    · unfold cost
      apply len
    · unfold Path.support
      apply supp


theorem non_cheapest_path_has_cheaper {u v : V} (p : G.Path u v):
  ¬ is_cheapest p → ∃ p' : G.Path u v, p'.cost < p.cost := by
  unfold is_cheapest
  simp

theorem non_cheapest_path_has_cheaper_cheapest {u v : V} (p : G.Path u v):
  ¬ is_cheapest p → ∃ p' : G.Path u v, is_cheapest p' ∧ p'.cost < p.cost := by
  intro prop
  --unfold is_cheapest
  obtain ⟨p',p'_cheaper⟩ := non_cheapest_path_has_cheaper p prop
  by_cases is_cheapest p'
  case pos cheapest =>
    grind
  case neg not_cheapest =>
    obtain ⟨p'',p''_cheapest, p''_lt⟩ := non_cheapest_path_has_cheaper_cheapest p' not_cheapest
    use p''
    constructor
    · exact p''_cheapest
    · apply lt_trans
      · exact p''_lt
      · exact p'_cheaper
termination_by p.cost



theorem sufficient_cheapest_path_cheaper {u v : V} (p : G.Path u v):
    (∀ p' : G.Path u v, is_cheapest p' → p'.cost ≥ p.cost) →
      is_cheapest p := by
  intro prop
  unfold is_cheapest
  intro p'
  by_cases is_cheapest p'
  case pos cheapest =>
    exact prop p' cheapest
  case neg not_cheapest =>
    obtain ⟨p'', p''_cheapest, p''_cheaper ⟩ := non_cheapest_path_has_cheaper_cheapest p' not_cheapest
    apply le_trans
    · exact prop p'' p''_cheapest
    · apply p''_cheapest p'


end Path

namespace Walk

theorem cheaper_path_exists (w : G.Walk u v):
  ∃ p : G.Path u v, p.cost ≤ w.cost := by
  let w' : G.Walk u v := w.bypass
  have nodup : w'.support.Nodup := by unfold w' ; apply bypass_isPath
  use ⟨ w', nodup ⟩
  unfold Path.cost
  apply cost_bypass_le


end Walk

namespace Path
/-
PROBLEM
A subpath (prefix) of a cheapest path is itself cheapest.

PROVIDED SOLUTION
By contradiction. Suppose q : g.Path u w with ¬(⟨uw, nodup⟩.cost ≤ q.cost), i.e. q.cost < uw.cost. Form walk q.val.append wv. Its cost is q.cost + wv.cost (by Walk.append_cost). Since uw.cost + wv.cost = (uw.append wv).cost = p.val.cost (using compose and Walk.append_cost), we have q.cost + wv.cost < uw.cost + wv.cost = p.val.cost. By Walk.cheaper_path_exists, obtain p' : g.Path u v with p'.cost ≤ (q.val.append wv).cost < p.cost. This contradicts p_cheapest p'.
-/
lemma subpath_of_cheapest_is_cheapest {u v w : V}
    (p : G.Path u v) (uw : G.Walk u w) (wv : G.Walk w v)
    (compose : uw.append wv = p.val)
    (nodup : uw.support.Nodup)
    (p_cheapest : p.is_cheapest) :
    Path.is_cheapest (⟨uw, nodup⟩ : G.Path u w) := by
      intro q
      by_contra hq
      -- Let's construct the walk $q.append wv$ and show that its cost is strictly less than $p$'s cost.
      have h_walk_cost : (q.val.append wv).cost < p.val.cost := by
        simp [cost_same, not_le] at hq
        apply lt_of_lt_of_eq ; rotate_left
        · rw [← compose]
        · repeat rw [Walk.append_cost ]
          apply add_lt_add_left
          exact hq
      -- By `Walk.cheaper_path_exists`, there exists a path `p'` with `p'.cost ≤ (q.val.append wv).cost`.
      obtain ⟨p', hp'⟩ : ∃ p' : G.Path u v, p'.cost ≤ (q.val.append wv).cost := by
        exact Walk.cheaper_path_exists (q.val.append wv)
      
      exact not_lt_of_ge ( p_cheapest p' ) ( lt_of_le_of_lt hp' h_walk_cost )


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


lemma cost_v_v (v : V) : G.cost_is v v 0 := by
  unfold cost_is
  use G.nil_path v
  unfold WeightedDiGraph.Path.is_cheapest
  constructor
  · simp_all only [WeightedDiGraph.Path.cost_same]
    rfl
  · intro p'
    simp_all only [WeightedDiGraph.Path.cost_same]
    apply le_trans (b:=0)
    · rfl
    · apply zero_le

end NatGraph

namespace NatGraph

def add_artificial_goal {V : Type} [FinEnum V] (G : NatGraph V) (goals : List V) : NatGraph (Option V) :=
  let nAdj : Option V → Option V → Prop := fun a b =>
    match (a,b) with
     | (none, none) => ⊥
     | (none, some _) => ⊥
     | (some g ,none) => g ∈ goals
     | (some a', some b') => G.Adj a' b'

  let g : Digraph (Option V) := Digraph.mk nAdj

  let nPay : (u v : Option V) -> (g.Adj u v) -> ℕ := fun u v adj =>
    match eq : (u,v) with
     | (none, none) => ⊥
     | (none, some _) => ⊥
     | (some g ,none) => 0 -- cost from actual goal to artificial one is 0
     | (some a', some b') =>
        have adj' : G.Adj a' b' := by
          unfold g nAdj at adj
          simp at adj
          split at adj <;> try contradiction
          · grind -- contradictory some = none
          · convert adj <;> grind
        G.Payload a' b' adj'

  let nDec : DecidableRel g.Adj := by
    unfold DecidableRel
    intro a b
    unfold g nAdj
    simp
    split
    · apply Decidable.isFalse
      simp
    · apply Decidable.isFalse
      simp
    · expose_names; exact List.instDecidableMemOfLawfulBEq g_1 goals
    · expose_names; apply G.instDecAdj a' b'

  WeightedDiGraph.mk g nPay nDec

def translate_path {V : Type} [FinEnum V] (G : NatGraph V) {a b : V} {goals : List V} (p : (G.add_artificial_goal goals).Path (some a) (some b)) (none_not_in_p : Option.none ∉ p.support) : G.Path a b :=  match eq : p.val with
  | .nil => WeightedDiGraph.nil_path a 
  | .cons adj walk => by
    expose_names   

    have w_is_some : w.isSome := by sorry
    let w' := w.get w_is_some

    let walk' : G.Walk w' b := by sorry
    have adj' : G.Adj a w' := by 
      unfold NatGraph.add_artificial_goal at adj
      simp at adj ; grind
    
    use WeightedDiGraph.Walk.cons adj' walk'
    sorry


end NatGraph
