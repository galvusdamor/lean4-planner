import pddl.SexpRoundTrip
import pddl.Eval

/-!
# Plan files

A *plan* produced by a planner is usually shipped as a text file in the syntax the
international planning competition uses: one ground action per line, written as an
s-expression, e.g.

```
; cost = 6 (general cost)
(pick-up a)
(stack a b)
```

This module reads such a file into the `List GroundAction` the semantics of `pddl.Semantics`
talks about, and turns the executable validator of `pddl.Eval` into a *verified plan
validator for plan files*:

* `PDDL.parsePlan` reads the plan text;
* `PDDL.printPlan` writes a plan back;
* `PDDL.validatePlanText` decides whether the plan in a text solves an instance, with
  `PDDL.validatePlanText_isPlan` (accepted ⇒ the parsed sequence really is a plan of the
  lifted semantics) and `PDDL.validatePlanText_not_isPlan` (rejected ⇒ it really is not);
* `PDDL.planCostText` reports its cost, which by `PDDL.planCostText_eq` is the cost the
  semantics assigns to it.

Because the tokeniser drops `;` comments, the cost lines that planners emit are ignored.
Tokens outside a parenthesised group — the step numbers of the `N: (action …)` format, or the
duration annotations `[1.0]` of temporal plans — are ignored as well, so those variants are
read too.
-/

namespace PDDL

/-- Read one ground action from an s-expression. -/
def groundActionOfSexp : Sexp → Except String GroundAction
  | .node (.atom n :: args) => do
      let as ← args.mapM fun s =>
        match s with
        | .atom a => .ok a
        | .node _ => .error s!"argument of '{n}' is not an object name: {s}"
      .ok ⟨n, as⟩
  | s => .error s!"not a ground action: {s}"

/-- Read the text of a plan file: every parenthesised group is a ground action, and
everything else (step numbers, duration annotations, comments) is ignored. -/
def parsePlan (txt : String) : Except String (List GroundAction) := do
  let xs ← parseSexps txt
  (xs.filter fun s => match s with | .node _ => true | .atom _ => false).mapM groundActionOfSexp

/-- Write a plan in the syntax `parsePlan` reads. -/
def printPlan (π : List GroundAction) : String :=
  String.intercalate "\n" (π.map GroundAction.toString) ++ "\n"

/-- Validate the plan written in `txt` against the instance `I`: `.error` if the text is not a
plan file, otherwise whether the plan it contains solves `I`. -/
def validatePlanText (I : Instance) (txt : String) : Except String Bool :=
  match parsePlan txt with
  | .error e => .error e
  | .ok π => .ok (I.validPlanB π)

/-- **Soundness of the plan-file validator**: if it accepts, the sequence of ground actions in
the file really is a plan of the instance in the sense of the lifted semantics. -/
theorem validatePlanText_isPlan {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    {txt : String} (h : validatePlanText I txt = .ok true) :
    ∃ π, parsePlan txt = .ok π ∧ I.IsPlan π := by
  cases hp : parsePlan txt with
  | error e => simp only [validatePlanText, hp, reduceCtorEq] at h
  | ok π =>
      refine ⟨π, rfl, (Instance.validPlanB_iff hwf π).1 ?_⟩
      simpa only [validatePlanText, hp, Except.ok.injEq] using h

/-- **Completeness of the plan-file validator**: if it rejects, the sequence of ground actions
in the file really is not a plan of the instance. -/
theorem validatePlanText_not_isPlan {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    {txt : String} (h : validatePlanText I txt = .ok false) :
    ∀ π, parsePlan txt = .ok π → ¬ I.IsPlan π := by
  intro π hp hplan
  have hv : I.validPlanB π = true := (Instance.validPlanB_iff hwf π).2 hplan
  simp only [validatePlanText, hp, hv, Except.ok.injEq] at h
  exact absurd h (by simp)

/-- The cost of the plan written in `txt`, or `.error` if the text is not a plan file. -/
def planCostText (I : Instance) (txt : String) : Except String Int :=
  match parsePlan txt with
  | .error e => .error e
  | .ok π => .ok (I.planCostB π)

/-- The cost reported for a plan file is the cost the semantics assigns to the plan in it. -/
theorem planCostText_eq {I : Instance} (hwf : I.domain.typesWellFormedB = true)
    {txt : String} {π : List GroundAction} (hp : parsePlan txt = .ok π) :
    planCostText I txt = .ok (I.planCost π) := by
  simp only [planCostText, hp, Instance.planCostB_eq hwf]

/-! ## Round trip

A printed plan is read back unchanged, provided every name occurring in it is a token the
tokeniser produces (`PDDL.okNameB`): nonempty, lower case and free of whitespace, parentheses
and `;`.  This is `PDDL.parsePlan_printPlan`, and it rests on the s-expression round trip
`PDDL.parseSexps_render` of `pddl.SexpRoundTrip`. -/

/-- Every name of a ground action is a token. -/
def actionNamesOkB (a : GroundAction) : Bool :=
  okNameB a.name && a.args.all okNameB

/-- Every name of a plan is a token. -/
def planNamesOkB (π : List GroundAction) : Bool :=
  π.all actionNamesOkB

/-- A ground action as an s-expression. -/
def sexpOfAction (a : GroundAction) : Sexp :=
  .node ((a.name :: a.args).map Sexp.atom)

theorem groundActionOfSexp_sexpOfAction (a : GroundAction) :
    groundActionOfSexp (sexpOfAction a) = .ok a := by
  have h : ∀ l : List Name,
      (l.map Sexp.atom).mapM
        (fun s => match s with
          | .atom x => (.ok x : Except String Name)
          | .node _ => .error s!"argument of '{a.name}' is not an object name: {s}") = .ok l := by
    intro l
    induction l with
    | nil => rfl
    | cons x l ih =>
        simp only [List.map_cons, List.mapM_cons, ih]
        rfl
  simp only [sexpOfAction, groundActionOfSexp, List.map_cons, h a.args]
  rfl

theorem toString_sexpOfAction (a : GroundAction) :
    (sexpOfAction a).toString = a.toString := by
  rw [sexpOfAction, show (Sexp.node ((a.name :: a.args).map Sexp.atom)).toString
      = "(" ++ String.intercalate " " (((a.name :: a.args).map Sexp.atom).map Sexp.toString)
        ++ ")" by simp [Sexp.toString]]
  rw [List.map_map]
  rw [show (Sexp.toString ∘ Sexp.atom) = id by funext s; simp [Sexp.toString]]
  simp [GroundAction.toString]

theorem atomsOk_sexpOfAction {a : GroundAction} (h : actionNamesOkB a = true) :
    AtomsOk (sexpOfAction a) := by
  have hpair : okNameB a.name = true ∧ ∀ x ∈ a.args, okNameB x = true := by
    simpa [actionNamesOkB] using h
  obtain ⟨hname, hargs⟩ := hpair
  refine AtomsOk.node ?_
  intro y hy
  rcases List.mem_map.mp hy with ⟨s, hs, rfl⟩
  rcases List.mem_cons.mp hs with rfl | hs'
  · exact AtomsOk.atom hname
  · exact AtomsOk.atom (hargs s hs')

/-- **A printed plan is read back unchanged.** -/
theorem parsePlan_printPlan (π : List GroundAction) (h : planNamesOkB π = true) :
    parsePlan (printPlan π) = .ok π := by
  have hok : ∀ x ∈ π.map sexpOfAction, AtomsOk x := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨a, ha, rfl⟩
    exact atomsOk_sexpOfAction (by simpa [planNamesOkB] using (List.all_eq_true.mp h) a ha)
  have hrender : printPlan π = render '\n' (π.map sexpOfAction) ++ "\n" := by
    rw [printPlan, render, List.map_map]
    congr 2
    exact List.map_congr_left (fun a _ => (toString_sexpOfAction a).symm)
  have hsexps : parseSexps (printPlan π) = .ok (π.map sexpOfAction) := by
    rw [hrender]
    exact parseSexps_render '\n' (by simp [Token.isWhitespace]) _ hok "\n" (by simp [Token.isWhitespace])
  have hnodes : ((π.map sexpOfAction).filter
      fun s => match s with | .node _ => true | .atom _ => false) = π.map sexpOfAction := by
    apply List.filter_eq_self.mpr
    intro x hx
    rcases List.mem_map.mp hx with ⟨a, -, rfl⟩
    rfl
  have hmap : ∀ σ : List GroundAction, (σ.map sexpOfAction).mapM groundActionOfSexp = .ok σ := by
    intro σ
    induction σ with
    | nil => rfl
    | cons a σ ih =>
        simp only [List.map_cons, List.mapM_cons, groundActionOfSexp_sexpOfAction a, ih]
        rfl
  rw [parsePlan]
  simp only [hsexps]
  show ((π.map sexpOfAction).filter
      (fun s => match s with | .node _ => true | .atom _ => false)).mapM groundActionOfSexp
    = .ok π
  rw [hnodes]
  exact hmap π

end PDDL
