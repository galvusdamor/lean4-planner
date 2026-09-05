import pddl.Grounding.Compile

/-!
# Correctness of the formula and effect compilers

This module proves that the compilation of lifted goal descriptions (`groundFormula`) and
of lifted effects (`groundEffect`) in `pddl.Grounding.Compile` preserves the semantics of
`pddl.Semantics`:

* `groundFormula_holds`: the compiled disjunctive normal form holds in a state iff the
  lifted formula does;
* `groundEffect_spec`: the compiled conditional effects and cost compute the same add set,
  delete set and cost as the lifted effect, in every state.

The operator and plan level statements are in `pddl.Grounding.Correct`.
-/

namespace PDDL

/-! ### Compiling goal descriptions is correct -/

/-- Auxiliary statement for the universal quantifier case of `groundFormula_holds`. -/
theorem groundFormula_all_aux {I : Instance} {s : State} {v : Name} {f : Formula}
    {σ : Assign}
    (ih : ∀ τ : Assign, DnfHolds (groundFormula I τ f) s ↔ Formula.Holds I τ s f) :
    ∀ L : List Name,
      DnfHolds (L.foldr (fun o acc => dnfAnd (groundFormula I (σ.set v o) f) acc) dnfTrue) s ↔
        ∀ o ∈ L, Formula.Holds I (σ.set v o) s f := by
  intro L
  induction L with
  | nil => simp
  | cons o L ihL =>
    simp only [List.foldr_cons, dnfHolds_dnfAnd, ih, ihL, List.mem_cons, forall_eq_or_imp]

/-- Auxiliary statement for the existential quantifier case of `groundFormula_holds`. -/
theorem groundFormula_ex_aux {I : Instance} {s : State} {v : Name} {f : Formula}
    {σ : Assign}
    (ih : ∀ τ : Assign, DnfHolds (groundFormula I τ f) s ↔ Formula.Holds I τ s f) :
    ∀ L : List Name,
      DnfHolds (L.foldr (fun o acc => dnfOr (groundFormula I (σ.set v o) f) acc) dnfFalse) s ↔
        ∃ o ∈ L, Formula.Holds I (σ.set v o) s f := by
  intro L
  induction L with
  | nil => simp
  | cons o L ihL =>
    simp only [List.foldr_cons, dnfHolds_dnfOr, ih, ihL, List.mem_cons, exists_eq_or_imp]

/-- The compiled disjunctive normal form holds in a state exactly when the lifted formula
does. -/
theorem groundFormula_holds {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    (s : State) (f : Formula) (σ : Assign) :
    DnfHolds (groundFormula I σ f) s ↔ Formula.Holds I σ s f := by
  induction f generalizing σ with
  | top => simp [groundFormula]
  | bot => simp [groundFormula]
  | atom p args => simp [groundFormula, DnfHolds]
  | eq t₁ t₂ =>
    by_cases he : t₁.inst σ = t₂.inst σ <;> simp [groundFormula, he]
  | neg f ih => simp [groundFormula, ih]
  | conj f g ihf ihg => simp [groundFormula, ihf, ihg]
  | disj f g ihf ihg => simp [groundFormula, ihf, ihg]
  | imp f g ihf ihg =>
    simp only [groundFormula, dnfHolds_dnfOr, dnfHolds_dnfNot, ihf, ihg, Formula.holds_imp]
    tauto
  | all v ty f ih =>
    rw [groundFormula, groundFormula_all_aux (fun τ => ih τ)]
    simp only [Formula.holds_all]
    constructor
    · exact fun hL o ho => hL o ((Instance.mem_objectsOfTypeL_iff hwf o ty).2 ho)
    · exact fun hL o ho => hL o ((Instance.mem_objectsOfTypeL_iff hwf o ty).1 ho)
  | ex v ty f ih =>
    rw [groundFormula, groundFormula_ex_aux (fun τ => ih τ)]
    simp only [Formula.holds_ex]
    constructor
    · rintro ⟨o, ho, hf⟩
      exact ⟨o, (Instance.mem_objectsOfTypeL_iff hwf o ty).1 ho, hf⟩
    · rintro ⟨o, ho, hf⟩
      exact ⟨o, (Instance.mem_objectsOfTypeL_iff hwf o ty).2 ho, hf⟩

/-! ### Compiling effects is correct -/

/-- The atoms added by a list of ground conditional effects in the state `s`. -/
def addSetOf (l : List CondEff) (s : State) : Set Atom :=
  {a | ∃ ce ∈ l, ce.Triggered s ∧ a ∈ ce.add}

/-- The atoms deleted by a list of ground conditional effects in the state `s`. -/
def delSetOf (l : List CondEff) (s : State) : Set Atom :=
  {a | ∃ ce ∈ l, ce.Triggered s ∧ a ∈ ce.del}

@[simp] theorem addSetOf_nil (s : State) : addSetOf [] s = ∅ := by simp [addSetOf]

@[simp] theorem delSetOf_nil (s : State) : delSetOf [] s = ∅ := by simp [delSetOf]

@[simp] theorem addSetOf_append (l₁ l₂ : List CondEff) (s : State) :
    addSetOf (l₁ ++ l₂) s = addSetOf l₁ s ∪ addSetOf l₂ s := by
  ext a; simp only [addSetOf, Set.mem_setOf_eq, Set.mem_union, List.mem_append]; grind

@[simp] theorem delSetOf_append (l₁ l₂ : List CondEff) (s : State) :
    delSetOf (l₁ ++ l₂) s = delSetOf l₁ s ∪ delSetOf l₂ s := by
  ext a; simp only [delSetOf, Set.mem_setOf_eq, Set.mem_union, List.mem_append]; grind

theorem triggered_prefixCond {cs : List Lit} {ce : CondEff} {s : State} :
    (CondEff.prefixCond cs ce).Triggered s ↔ ClauseHolds cs s ∧ ce.Triggered s := by
  simp [CondEff.prefixCond, CondEff.Triggered]

theorem mem_guardCondEffs {d : Dnf} {l : List CondEff} {ce' : CondEff} :
    ce' ∈ guardCondEffs d l ↔ ∃ c ∈ d, ∃ ce ∈ l, ce' = CondEff.prefixCond c ce := by
  simp only [guardCondEffs, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨c, hc, ce, hce, rfl⟩; exact ⟨c, hc, ce, hce, rfl⟩
  · rintro ⟨c, hc, ce, hce, rfl⟩; exact ⟨c, hc, ce, hce, rfl⟩

theorem addSetOf_guardCondEffs_pos {d : Dnf} {l : List CondEff} {s : State}
    (h : DnfHolds d s) : addSetOf (guardCondEffs d l) s = addSetOf l s := by
  obtain ⟨c₀, hc₀, hc₀h⟩ := h
  ext a
  simp only [addSetOf, Set.mem_setOf_eq]
  constructor
  · rintro ⟨ce', hce', ht, hmem⟩
    obtain ⟨c, -, ce, hce, rfl⟩ := mem_guardCondEffs.1 hce'
    exact ⟨ce, hce, (triggered_prefixCond.1 ht).2, hmem⟩
  · rintro ⟨ce, hce, ht, hmem⟩
    exact ⟨CondEff.prefixCond c₀ ce, mem_guardCondEffs.2 ⟨c₀, hc₀, ce, hce, rfl⟩,
      triggered_prefixCond.2 ⟨hc₀h, ht⟩, hmem⟩

theorem delSetOf_guardCondEffs_pos {d : Dnf} {l : List CondEff} {s : State}
    (h : DnfHolds d s) : delSetOf (guardCondEffs d l) s = delSetOf l s := by
  obtain ⟨c₀, hc₀, hc₀h⟩ := h
  ext a
  simp only [delSetOf, Set.mem_setOf_eq]
  constructor
  · rintro ⟨ce', hce', ht, hmem⟩
    obtain ⟨c, -, ce, hce, rfl⟩ := mem_guardCondEffs.1 hce'
    exact ⟨ce, hce, (triggered_prefixCond.1 ht).2, hmem⟩
  · rintro ⟨ce, hce, ht, hmem⟩
    exact ⟨CondEff.prefixCond c₀ ce, mem_guardCondEffs.2 ⟨c₀, hc₀, ce, hce, rfl⟩,
      triggered_prefixCond.2 ⟨hc₀h, ht⟩, hmem⟩

theorem addSetOf_guardCondEffs_neg {d : Dnf} {l : List CondEff} {s : State}
    (h : ¬ DnfHolds d s) : addSetOf (guardCondEffs d l) s = ∅ := by
  ext a
  simp only [addSetOf, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists,
    not_and]
  rintro ce' hce' ht
  obtain ⟨c, hc, ce, -, rfl⟩ := mem_guardCondEffs.1 hce'
  exact absurd ⟨c, hc, (triggered_prefixCond.1 ht).1⟩ h

theorem delSetOf_guardCondEffs_neg {d : Dnf} {l : List CondEff} {s : State}
    (h : ¬ DnfHolds d s) : delSetOf (guardCondEffs d l) s = ∅ := by
  ext a
  simp only [delSetOf, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists,
    not_and]
  rintro ce' hce' ht
  obtain ⟨c, hc, ce, -, rfl⟩ := mem_guardCondEffs.1 hce'
  exact absurd ⟨c, hc, (triggered_prefixCond.1 ht).1⟩ h

theorem addSet_eq_addSetOf (op : GroundOp) (s : State) :
    op.addSet s = addSetOf op.effs s := rfl

theorem delSet_eq_delSetOf (op : GroundOp) (s : State) :
    op.delSet s = delSetOf op.effs s := rfl

/-- The specification of the effect compiler: the compiled conditional effects `l` and the
compiled cost `c` describe the lifted effect `e` in the state `s`. -/
structure GroundEffSpec (I : Instance) (σ : Assign) (s : State) (e : Effect)
    (l : List CondEff) (c : Int) : Prop where
  add : Effect.addSet I σ s e = addSetOf l s
  del : Effect.delSet I σ s e = delSetOf l s
  cost : Effect.cost I σ s e = c

/-- Auxiliary statement for the universally quantified effect case. -/
theorem groundEffect_all_aux {I : Instance} {s : State} {v : Name} {e : Effect} {σ : Assign}
    (ih : ∀ (τ : Assign) (l : List CondEff) (c : Int), groundEffect I τ e = some (l, c) →
      GroundEffSpec I τ s e l c) :
    ∀ (L : List Name) (l : List CondEff) (c : Int),
      L.foldr (fun o acc => do
        let (l, c) ← groundEffect I (σ.set v o) e
        let (l', c') ← acc
        pure (l ++ l', c + c')) (some ([], 0)) = some (l, c) →
      {a | ∃ o ∈ L, a ∈ Effect.addSet I (σ.set v o) s e} = addSetOf l s ∧
      {a | ∃ o ∈ L, a ∈ Effect.delSet I (σ.set v o) s e} = delSetOf l s ∧
      (L.map (fun o => Effect.cost I (σ.set v o) s e)).sum = c := by
  intro L
  induction L with
  | nil =>
    intro l c h
    simp only [List.foldr_nil, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨?_, ?_, by simp⟩ <;> · ext a; simp
  | cons o L ihL =>
    intro l c h
    simp only [List.foldr_cons] at h
    cases hr : groundEffect I (σ.set v o) e with
    | none => rw [hr] at h; simp at h
    | some p =>
      obtain ⟨l₁, c₁⟩ := p
      rw [hr] at h
      cases hrs : L.foldr (fun o acc => do
          let (l, c) ← groundEffect I (σ.set v o) e
          let (l', c') ← acc
          pure (l ++ l', c + c')) (some ([], 0)) with
      | none => rw [hrs] at h; simp at h
      | some q =>
        obtain ⟨l₂, c₂⟩ := q
        rw [hrs] at h
        simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨ha, hd, hc⟩ := ih _ _ _ hr
        obtain ⟨ha', hd', hc'⟩ := ihL _ _ hrs
        refine ⟨?_, ?_, ?_⟩
        · rw [addSetOf_append, ← ha, ← ha']
          ext a
          simp only [Set.mem_setOf_eq, Set.mem_union, List.mem_cons]
          constructor
          · rintro ⟨o', (rfl | ho'), hmem⟩
            · exact Or.inl hmem
            · exact Or.inr ⟨o', ho', hmem⟩
          · rintro (hmem | ⟨o', ho', hmem⟩)
            · exact ⟨o, Or.inl rfl, hmem⟩
            · exact ⟨o', Or.inr ho', hmem⟩
        · rw [delSetOf_append, ← hd, ← hd']
          ext a
          simp only [Set.mem_setOf_eq, Set.mem_union, List.mem_cons]
          constructor
          · rintro ⟨o', (rfl | ho'), hmem⟩
            · exact Or.inl hmem
            · exact Or.inr ⟨o', ho', hmem⟩
          · rintro (hmem | ⟨o', ho', hmem⟩)
            · exact ⟨o, Or.inl rfl, hmem⟩
            · exact ⟨o', Or.inr ho', hmem⟩
        · simp only [List.map_cons, List.sum_cons, hc, hc']

/-- The effect compiler is correct: the compiled conditional effects and cost describe the
lifted effect in every state. -/
theorem groundEffect_spec {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    (s : State) (e : Effect) (σ : Assign) (l : List CondEff) (c : Int)
    (h : groundEffect I σ e = some (l, c)) : GroundEffSpec I σ s e l c := by
  induction e generalizing σ l c with
  | nil =>
    simp only [groundEffect, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by simp [Effect.addSet], by simp [Effect.delSet], rfl⟩
  | add p args =>
    simp only [groundEffect, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨?_, ?_, rfl⟩ <;>
      · ext a
        simp [Effect.addSet, Effect.delSet, addSetOf, delSetOf, CondEff.Triggered]
  | del p args =>
    simp only [groundEffect, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨?_, ?_, rfl⟩ <;>
      · ext a
        simp [Effect.addSet, Effect.delSet, addSetOf, delSetOf, CondEff.Triggered]
  | conj e₁ e₂ ih₁ ih₂ =>
    simp only [groundEffect] at h
    cases h₁ : groundEffect I σ e₁ with
    | none => rw [h₁] at h; simp at h
    | some p₁ =>
      obtain ⟨l₁, c₁⟩ := p₁
      cases h₂ : groundEffect I σ e₂ with
      | none => rw [h₁, h₂] at h; simp at h
      | some p₂ =>
        obtain ⟨l₂, c₂⟩ := p₂
        rw [h₁, h₂] at h
        simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨ha₁, hd₁, hc₁⟩ := ih₁ σ l₁ c₁ h₁
        obtain ⟨ha₂, hd₂, hc₂⟩ := ih₂ σ l₂ c₂ h₂
        exact ⟨by simp [Effect.addSet, ha₁, ha₂], by simp [Effect.delSet, hd₁, hd₂],
          by simp [Effect.cost, hc₁, hc₂]⟩
  | all v ty e ih =>
    simp only [groundEffect] at h
    obtain ⟨ha, hd, hc⟩ := groundEffect_all_aux (fun τ l c hl => ih τ l c hl) _ _ _ h
    refine ⟨?_, ?_, ?_⟩
    · rw [← ha]
      ext a
      simp only [Effect.addSet, Set.mem_setOf_eq]
      constructor
      · rintro ⟨o, ho, hmem⟩
        exact ⟨o, (Instance.mem_objectsOfTypeL_iff hwf o ty).2 ho, hmem⟩
      · rintro ⟨o, ho, hmem⟩
        exact ⟨o, (Instance.mem_objectsOfTypeL_iff hwf o ty).1 ho, hmem⟩
    · rw [← hd]
      ext a
      simp only [Effect.delSet, Set.mem_setOf_eq]
      constructor
      · rintro ⟨o, ho, hmem⟩
        exact ⟨o, (Instance.mem_objectsOfTypeL_iff hwf o ty).2 ho, hmem⟩
      · rintro ⟨o, ho, hmem⟩
        exact ⟨o, (Instance.mem_objectsOfTypeL_iff hwf o ty).1 ho, hmem⟩
    · rw [← hc]
      simp only [Effect.cost, Instance.objectsOfTypeL_eq_objectsOfType hwf]
  | when cnd e ih =>
    simp only [groundEffect] at h
    have hr : DnfHolds (groundFormula I σ cnd) s ↔ Formula.Holds I σ s cnd :=
      groundFormula_holds hwf s cnd σ
    cases he : groundEffect I σ e with
    | none => rw [he] at h; simp at h
    | some p =>
      obtain ⟨l', c'⟩ := p
      rw [he] at h
      simp only [Option.bind_eq_bind, Option.bind_some] at h
      obtain ⟨ha, hd, hcst⟩ := ih σ l' c' he
      by_cases hc0 : c' = 0
      · subst hc0
        simp only [Option.pure_def] at h
        obtain ⟨rfl, rfl⟩ := h
        by_cases hcond : Formula.Holds I σ s cnd
        · have hdh : DnfHolds (groundFormula I σ cnd) s := hr.2 hcond
          refine ⟨?_, ?_, ?_⟩
          · rw [addSetOf_guardCondEffs_pos hdh, ← ha]
            ext a; simp [Effect.addSet, hcond]
          · rw [delSetOf_guardCondEffs_pos hdh, ← hd]
            ext a; simp [Effect.delSet, hcond]
          · simp [Effect.cost, hcond, hcst]
        · have hdh : ¬ DnfHolds (groundFormula I σ cnd) s := fun hh => hcond (hr.1 hh)
          refine ⟨?_, ?_, ?_⟩
          · rw [addSetOf_guardCondEffs_neg hdh]
            ext a; simp [Effect.addSet, hcond]
          · rw [delSetOf_guardCondEffs_neg hdh]
            ext a; simp [Effect.delSet, hcond]
          · simp [Effect.cost, hcond]
      · rw [if_neg hc0] at h
        cases hd0 : groundFormula I σ cnd with
        | nil =>
          rw [hd0] at h
          simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hcond : ¬ Formula.Holds I σ s cnd := by
            intro hh
            have := hr.2 hh
            rw [hd0] at this
            simp at this
          exact ⟨by simp [Effect.addSet, hcond], by simp [Effect.delSet, hcond],
            by simp [Effect.cost, hcond]⟩
        | cons c₀ d₀ =>
          cases c₀ with
          | nil =>
            cases d₀ with
            | nil =>
              rw [hd0] at h
              simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hcond : Formula.Holds I σ s cnd := by
                refine hr.1 ?_
                rw [hd0]
                exact ⟨[], by simp, by simp⟩
              exact ⟨by rw [← ha]; ext a; simp [Effect.addSet, hcond],
                by rw [← hd]; ext a; simp [Effect.delSet, hcond],
                by simp [Effect.cost, hcond, hcst]⟩
            | cons c₁ d₁ => rw [hd0] at h; simp at h
          | cons l₀ c₀' => rw [hd0] at h; simp at h
  | incCost ne =>
    simp only [groundEffect, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by simp [Effect.addSet], by simp [Effect.delSet], rfl⟩

end PDDL
