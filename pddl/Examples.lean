import pddl.Parser
import pddl.Eval

/-!
# Worked example: parsing and executing a small PDDL instance

This module contains a small, self-contained PDDL domain and problem that exercise typing,
equality, negative preconditions, universally quantified conditional effects, existential
goals and action costs.  The source text is parsed by `pddl.Parser`, and the resulting
instance is then reasoned about with the semantics of `pddl.Semantics` — the statements
below are theorems about `Instance.IsPlan` and `Instance.planCost`, discharged through the
verified executable evaluator of `pddl.Eval`.
-/

namespace PDDL
namespace Examples

/-- A small transport-like domain. -/
def transportLiteDomainSrc : String :=
"(define (domain transport-lite)
 (:requirements :typing :equality :adl :action-costs)
 (:types location vehicle package - object)
 (:predicates
   (road ?l1 ?l2 - location)
   (at ?x - object ?l - location)
   (in ?p - package ?v - vehicle)
   (visited ?l - location))
 (:functions
   (road-length ?l1 ?l2 - location) - number
   (total-cost) - number)
 (:action drive
   :parameters (?v - vehicle ?from ?to - location)
   :precondition (and (at ?v ?from) (road ?from ?to) (not (= ?from ?to)))
   :effect (and (not (at ?v ?from)) (at ?v ?to) (visited ?to)
                (forall (?p - package)
                  (when (in ?p ?v) (and (not (at ?p ?from)) (at ?p ?to))))
                (increase (total-cost) (road-length ?from ?to))))
 (:action load
   :parameters (?v - vehicle ?p - package ?l - location)
   :precondition (and (at ?v ?l) (at ?p ?l))
   :effect (and (not (at ?p ?l)) (in ?p ?v) (increase (total-cost) 1)))
 (:action unload
   :parameters (?v - vehicle ?p - package ?l - location)
   :precondition (and (at ?v ?l) (in ?p ?v))
   :effect (and (not (in ?p ?v)) (at ?p ?l) (increase (total-cost) 1))))"

/-- A small problem for `transportLiteDomainSrc`. -/
def transportLiteProblemSrc : String :=
"(define (problem deliver-one)
 (:domain transport-lite)
 (:objects
   loc1 loc2 - location
   truck - vehicle
   pkg - package)
 (:init
   (= (total-cost) 0)
   (road loc1 loc2)
   (road loc2 loc1)
   (= (road-length loc1 loc2) 5)
   (= (road-length loc2 loc1) 5)
   (at truck loc1)
   (at pkg loc1))
 (:goal (and (at pkg loc2) (exists (?l - location) (visited ?l))))
 (:metric minimize (total-cost)))"

#eval parseDomain transportLiteDomainSrc |>.toOption.map (·.actions.map (·.name))
#eval parseProblem transportLiteProblemSrc |>.toOption.map (·.objects.length)

/-- The parsed domain. -/
def transportLiteDomain : Domain :=
  (parseDomain transportLiteDomainSrc).toOption.getD (emptyDomain "parse-error")

/-- The parsed problem. -/
def transportLiteProblem : Problem :=
  (parseProblem transportLiteProblemSrc).toOption.getD (emptyProblem "parse-error")

/-- The parsed planning instance. -/
def transportLite : Instance := ⟨transportLiteDomain, transportLiteProblem⟩

/-- Both files parse without errors. -/
theorem transportLite_parses :
    (parseDomain transportLiteDomainSrc).isOk = true ∧
      (parseProblem transportLiteProblemSrc).isOk = true := by
  native_decide

/-- The type hierarchy of the example domain is well formed, so the executable evaluator
decides the semantics for this instance. -/
theorem transportLite_typesWellFormed : transportLite.domain.typesWellFormedB = true := by
  native_decide

/-- A three step plan for the example problem. -/
def transportLitePlan : List GroundAction :=
  [⟨"load", ["truck", "pkg", "loc1"]⟩,
   ⟨"drive", ["truck", "loc1", "loc2"]⟩,
   ⟨"unload", ["truck", "pkg", "loc2"]⟩]

/-- The plan solves the example problem, in the sense of the lifted PDDL semantics. -/
theorem transportLitePlan_isPlan : transportLite.IsPlan transportLitePlan := by
  rw [← Instance.validPlanB_iff transportLite_typesWellFormed]
  native_decide

/-- Its cost is `1 + 5 + 1 = 7`. -/
theorem transportLitePlan_cost : transportLite.planCost transportLitePlan = 7 := by
  rw [← Instance.planCostB_eq transportLite_typesWellFormed]
  native_decide

/-- Dropping the `load` step does not yield a plan: the package stays at `loc1`. -/
theorem transportLitePlan_tail_not_plan :
    ¬ transportLite.IsPlan transportLitePlan.tail := by
  rw [← Instance.validPlanB_iff transportLite_typesWellFormed]
  native_decide

/-- Driving from a location the truck is not at is not applicable. -/
theorem drive_from_loc2_not_applicable :
    ¬ transportLite.Applicable ⟨"drive", ["truck", "loc2", "loc1"]⟩ transportLite.initState := by
  rw [← Instance.toState_initStateB,
    ← Instance.applicableB_iff transportLite_typesWellFormed]
  native_decide

end Examples
end PDDL
