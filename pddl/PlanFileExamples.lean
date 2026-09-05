import pddl.Examples
import pddl.PlanFile

/-!
# Worked example: validating a plan file

The instance of `pddl.Examples` again, but the plan now comes as the *text* of a plan file in
the syntax planners emit.  The statements are theorems about the lifted semantics
(`Instance.IsPlan`, `Instance.planCost`), obtained from the verified plan-file validator of
`pddl.PlanFile`.
-/

namespace PDDL
namespace Examples

/-- A plan file for `transportLite`, in the syntax a planner emits: step numbers, duration
annotations and a cost comment are ignored by the reader. -/
def transportLitePlanFile : String :=
"; cost = 7 (general cost)
0.00000: (load truck pkg loc1) [1.00000]
1.00000: (drive truck loc1 loc2) [1.00000]
2.00000: (unload truck pkg loc2) [1.00000]
"

/-- The plan file is read as the plan of `pddl.Examples`. -/
theorem parsePlan_transportLitePlanFile :
    parsePlan transportLitePlanFile = .ok transportLitePlan := by
  native_decide

/-- The validator accepts the plan file. -/
theorem validate_transportLitePlanFile :
    validatePlanText transportLite transportLitePlanFile = .ok true := by
  native_decide

/-- Hence the actions in the file really solve the instance, in the sense of the lifted
semantics. -/
theorem transportLitePlanFile_isPlan : transportLite.IsPlan transportLitePlan := by
  obtain ⟨π, hπ, hplan⟩ :=
    validatePlanText_isPlan transportLite_typesWellFormed validate_transportLitePlanFile
  rw [parsePlan_transportLitePlanFile, Except.ok.injEq] at hπ
  subst hπ
  exact hplan

/-- The cost reported for the plan file is the cost the semantics assigns to the plan. -/
theorem planCostText_transportLitePlanFile :
    planCostText transportLite transportLitePlanFile = .ok (transportLite.planCost transportLitePlan) :=
  planCostText_eq transportLite_typesWellFormed parsePlan_transportLitePlanFile

/-- A plan file whose first step is missing is rejected. -/
def transportLiteBadPlanFile : String :=
"(drive truck loc1 loc2)
(unload truck pkg loc2)
"

theorem validate_transportLiteBadPlanFile :
    validatePlanText transportLite transportLiteBadPlanFile = .ok false := by
  native_decide

/-- And the sequence of actions it contains really is not a plan. -/
theorem transportLiteBadPlanFile_not_isPlan :
    ∀ π, parsePlan transportLiteBadPlanFile = .ok π → ¬ transportLite.IsPlan π :=
  validatePlanText_not_isPlan transportLite_typesWellFormed validate_transportLiteBadPlanFile

/-- Printing the plan and reading it back gives the plan. -/
theorem roundTrip_transportLitePlan :
    parsePlan (printPlan transportLitePlan) = .ok transportLitePlan :=
  parsePlan_printPlan transportLitePlan (by native_decide)

end Examples
end PDDL
