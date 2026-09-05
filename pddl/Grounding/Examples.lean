import pddl.Grounding.Positive
import pddl.Examples

/-!
# Worked examples for the grounder

Two examples are grounded here.

* The `transport-lite` instance of `pddl.Examples` uses conditional effects, so its
  grounding produces a `GroundTask` with conditional effects, which cannot be translated to
  `STRIPS.PlanningTask`.  Its ground task is nevertheless solvable, which follows from the
  plan of the lifted instance by `PDDL.groundInstance_solvable_iff` — no extra computation
  is needed.
* A small blocks world instance without conditional effects is grounded, translated to
  `STRIPS.PlanningTask`, and the translated task is shown to be solvable.
* A small instance with a negative and a disjunctive precondition is grounded, compiled to
  positive normal form and translated to `STRIPS.PlanningTask`, which is again shown to be
  solvable.
-/

namespace PDDL
namespace Examples

/-! ### Grounding the conditional-effect example -/

/-- The goal of the `transport-lite` problem of `pddl.Examples` is an existentially
quantified formula `(exists (?l - location) (visited ?l))`.  It is expanded into a
disjunction over the two locations, i.e. into a goal with two clauses in disjunctive
normal form. -/
theorem transportLite_groundInstance_disjunctive_goal :
    ((groundInstance transportLite).map (fun T => T.goal.length)) = some 2 := by
  native_decide

/-- The same problem with a conjunctive goal. -/
def transportLiteConjProblemSrc : String :=
"(define (problem deliver-one-conj)
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
 (:goal (and (at pkg loc2) (visited loc2)))
 (:metric minimize (total-cost)))"

/-- The `transport-lite` instance with a conjunctive goal. -/
def transportLiteConj : Instance :=
  ⟨transportLiteDomain,
   (parseProblem transportLiteConjProblemSrc).toOption.getD (emptyProblem "parse-error")⟩

theorem transportLiteConj_typesWellFormed :
    transportLiteConj.domain.typesWellFormedB = true := by
  native_decide

/-- The three step plan also solves the variant with the conjunctive goal. -/
theorem transportLiteConjPlan_isPlan : transportLiteConj.IsPlan transportLitePlan := by
  rw [← Instance.validPlanB_iff transportLiteConj_typesWellFormed]
  native_decide

/-- The grounding of the conditional-effect example. -/
def transportLiteGround : GroundTask :=
  (groundInstance transportLiteConj).getD default

theorem transportLiteConj_groundInstance :
    groundInstance transportLiteConj = some transportLiteGround := by
  native_decide

#eval transportLiteGround.ops.length
#eval transportLiteGround.atoms.length

/-- The ground task of the conditional-effect example is solvable; this follows from the
plan of the lifted instance. -/
theorem transportLiteGround_solvable : transportLiteGround.Solvable :=
  (groundInstance_solvable_iff transportLiteConj_typesWellFormed
    transportLiteConj_groundInstance).1 ⟨_, transportLiteConjPlan_isPlan⟩

/-- The example does use conditional effects, so it is not a STRIPS task. -/
theorem transportLiteGround_not_unconditional : ¬ transportLiteGround.Unconditional := by
  rw [← GroundTask.unconditionalB_iff]
  native_decide

/-! ### A blocks world example without conditional effects -/

/-- A blocks world domain, in the STRIPS fragment. -/
def blocksDomainSrc : String :=
"(define (domain blocks-lite)
 (:requirements :strips :typing)
 (:types block)
 (:predicates
   (on ?x ?y - block)
   (ontable ?x - block)
   (clear ?x - block)
   (handempty)
   (holding ?x - block))
 (:action pick-up
   :parameters (?x - block)
   :precondition (and (clear ?x) (ontable ?x) (handempty))
   :effect (and (not (ontable ?x)) (not (clear ?x)) (not (handempty)) (holding ?x)))
 (:action put-down
   :parameters (?x - block)
   :precondition (holding ?x)
   :effect (and (not (holding ?x)) (clear ?x) (handempty) (ontable ?x)))
 (:action stack
   :parameters (?x ?y - block)
   :precondition (and (holding ?x) (clear ?y))
   :effect (and (not (holding ?x)) (not (clear ?y)) (clear ?x) (handempty) (on ?x ?y)))
 (:action unstack
   :parameters (?x ?y - block)
   :precondition (and (on ?x ?y) (clear ?x) (handempty))
   :effect (and (holding ?x) (clear ?y) (not (clear ?x)) (not (handempty))
                (not (on ?x ?y)))))"

/-- A two block problem: stack `a` onto `b`. -/
def blocksProblemSrc : String :=
"(define (problem stack-two)
 (:domain blocks-lite)
 (:objects a b - block)
 (:init (ontable a) (ontable b) (clear a) (clear b) (handempty))
 (:goal (on a b)))"

/-- The parsed blocks instance. -/
def blocks : Instance :=
  ⟨(parseDomain blocksDomainSrc).toOption.getD (emptyDomain "parse-error"),
   (parseProblem blocksProblemSrc).toOption.getD (emptyProblem "parse-error")⟩

theorem blocks_parses :
    (parseDomain blocksDomainSrc).isOk = true ∧
      (parseProblem blocksProblemSrc).isOk = true := by
  native_decide

theorem blocks_typesWellFormed : blocks.domain.typesWellFormedB = true := by
  native_decide

/-- A two step plan for the blocks problem. -/
def blocksPlan : List GroundAction :=
  [⟨"pick-up", ["a"]⟩, ⟨"stack", ["a", "b"]⟩]

/-- The plan solves the lifted blocks instance. -/
theorem blocksPlan_isPlan : blocks.IsPlan blocksPlan := by
  rw [← Instance.validPlanB_iff blocks_typesWellFormed]
  native_decide

/-- The grounding of the blocks instance. -/
def blocksGround : GroundTask := (groundInstance blocks).getD default

theorem blocks_groundInstance : groundInstance blocks = some blocksGround := by
  native_decide

#eval blocksGround.ops.length
#eval blocksGround.atoms.length

/-- The blocks grounding has no conditional effects, no negative conditions and a
conjunctive goal, so it can be translated to STRIPS. -/
theorem blocksGround_stripsReady : blocksGround.StripsReady := by
  rw [← GroundTask.stripsReadyB_iff]
  native_decide

/-- The STRIPS planning task obtained from the blocks instance. -/
def blocksStrips : STRIPS.PlanningTask blocksGround.numVars := blocksGround.toSTRIPS

/-- The STRIPS task obtained by grounding the blocks instance is solvable — a consequence
of the plan for the lifted PDDL instance. -/
theorem blocksStrips_solvable :
    Nonempty (STRIPS.PlanningTask.Plan blocksStrips blocksStrips.init) :=
  (groundInstance_strips_solvable_iff blocks_typesWellFormed blocks_groundInstance
    blocksGround_stripsReady).2 ⟨_, blocksPlan_isPlan⟩

/-! ### An example with negative and disjunctive preconditions -/

/-- A tiny robot domain using a negative precondition (`(not (clean ?r))`) and a
disjunctive precondition (`(or (connected ?x ?y) (connected ?y ?x))`). -/
def robotDomainSrc : String :=
"(define (domain robot)
 (:requirements :strips :typing :equality :negative-preconditions :disjunctive-preconditions)
 (:types room)
 (:predicates
   (at ?r - room)
   (connected ?x ?y - room)
   (clean ?r - room))
 (:action move
   :parameters (?from ?to - room)
   :precondition (and (at ?from) (not (= ?from ?to))
                      (or (connected ?from ?to) (connected ?to ?from)))
   :effect (and (not (at ?from)) (at ?to)))
 (:action tidy
   :parameters (?r - room)
   :precondition (and (at ?r) (not (clean ?r)))
   :effect (clean ?r)))"

/-- Two rooms, connected in one direction; the robot has to move and tidy. -/
def robotProblemSrc : String :=
"(define (problem tidy-b)
 (:domain robot)
 (:objects a b - room)
 (:init (at a) (connected a b))
 (:goal (and (at b) (clean b))))"

/-- The parsed robot instance. -/
def robot : Instance :=
  ⟨(parseDomain robotDomainSrc).toOption.getD (emptyDomain "parse-error"),
   (parseProblem robotProblemSrc).toOption.getD (emptyProblem "parse-error")⟩

theorem robot_parses :
    (parseDomain robotDomainSrc).isOk = true ∧
      (parseProblem robotProblemSrc).isOk = true := by
  native_decide

theorem robot_typesWellFormed : robot.domain.typesWellFormedB = true := by
  native_decide

/-- A two step plan for the robot problem. -/
def robotPlan : List GroundAction := [⟨"move", ["a", "b"]⟩, ⟨"tidy", ["b"]⟩]

/-- The plan solves the lifted robot instance. -/
theorem robotPlan_isPlan : robot.IsPlan robotPlan := by
  rw [← Instance.validPlanB_iff robot_typesWellFormed]
  native_decide

/-- The grounding of the robot instance. -/
def robotGround : GroundTask := (groundInstance robot).getD default

theorem robot_groundInstance : groundInstance robot = some robotGround := by
  native_decide

#eval robotGround.ops.length
#eval robotGround.atoms.length

/-- The grounding contains negative literals (from `(not (clean ?r))`), so it is not a
STRIPS task; the disjunctive precondition of `move` was multiplied out into one operator
per disjunct. -/
theorem robotGround_not_positive : ¬ robotGround.Positive := by
  rw [← GroundTask.positiveB_iff]
  native_decide

/-- It has no conditional effects, does not use the reserved predicate name of the
positive normal form, and has a conjunctive goal, so it can be compiled to positive normal
form and then translated to STRIPS. -/
theorem robotGround_unconditional : robotGround.Unconditional := by
  rw [← GroundTask.unconditionalB_iff]
  native_decide

theorem robotGround_negFresh : robotGround.NegFresh := by
  rw [← GroundTask.negFreshB_iff]
  native_decide

theorem robotGround_conjunctiveGoal : robotGround.ConjunctiveGoal := by
  rw [← GroundTask.conjunctiveGoalB_iff]
  native_decide

/-- The positive normal form of the robot grounding. -/
def robotPositive : GroundTask := robotGround.toPositive

#eval robotPositive.ops.length
#eval robotPositive.atoms.length

/-- It is a STRIPS task; this needs no computation, it holds for every positive normal
form of an unconditional task with a conjunctive goal. -/
theorem robotPositive_stripsReady : robotPositive.StripsReady :=
  GroundTask.toPositive_stripsReady robotGround_conjunctiveGoal

/-- The STRIPS planning task obtained from the robot instance. -/
def robotStrips : STRIPS.PlanningTask robotPositive.numVars := robotPositive.toSTRIPS

/-- The STRIPS task obtained by grounding the robot instance and removing the negative
preconditions is solvable — a consequence of the plan for the lifted PDDL instance. -/
theorem robotStrips_solvable :
    Nonempty (STRIPS.PlanningTask.Plan robotStrips robotStrips.init) :=
  (groundInstance_positive_strips_solvable_iff robot_typesWellFormed robot_groundInstance
    robotGround_negFresh robotGround_unconditional robotGround_conjunctiveGoal).2
    ⟨_, robotPlan_isPlan⟩

end Examples
end PDDL
