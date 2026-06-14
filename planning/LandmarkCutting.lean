import planning.Landmark


namespace Validator



def i_g_normal_form {n : ℕ} (prob : STRIPS n) : STRIPS (n+2) :=
  let goal_pre : VarSet' (n + 2) := 
       ⟨ prob.goal'.val.map (fun x : Fin n => ⟨x.val, by grind ⟩), by sorry⟩ -- the current goal is the precondition of the goal action

  STRIPS.mk
    (prob.varNames.append (⟨#["i","g"] , by rfl⟩))
    ((prob.actions'.map (fun a =>
      Action.mk  a.name
        ⟨ (a.pre'.val.map (fun a : Fin n => ⟨a.val,by grind⟩)) ++ [⟨n, by simp⟩], by sorry⟩ -- every action gets n as an additional precondition
        ⟨ a.add'.val.map (fun a : Fin n => ⟨a.val,by grind⟩), by sorry⟩
        ⟨ a.del'.val.map (fun a : Fin n => ⟨a.val,by grind⟩), by sorry⟩
        a.cost
      )) ++
      [Action.mk 
        "init"
        (⟨[⟨ n, by simp⟩ ], by grind⟩) -- pre is only init
        (varset'_of_state' ((prob.init'.concat false).concat false))
        ⟨[],by apply List.sortedLT_iff_pairwise.mpr ; simp⟩ -- no deletes
        0,
        Action.mk
        "goal"
        goal_pre 
        (⟨[⟨ n+1, by simp⟩ ], by grind⟩) -- add is only goal
        ⟨[],by apply List.sortedLT_iff_pairwise.mpr ; simp⟩ -- no deletes
        0
      ]
    )
    (BitVec.zero (n+2) ||| (BitVec.twoPow (n+2) (n))) -- the initial state now contains only i
    (⟨[⟨ n+1, by simp⟩ ], by grind⟩) -- only g is now a goal



lemma i_g_normal_form_keeps_h_plus {n : ℕ} {prob : STRIPS n} :
   h_plus prob prob.init' = h_plus (i_g_normal_form prob) (i_g_normal_form prob).init'  := by sorry




abbrev precondition_choice_function {n : ℕ} {prob : STRIPS n}
  (a : {b : Action n // b ∈ prob.actions'}) : Type := { p : Fin n // p ∈ a.val.pre}


