;; A test domain that exercises syntactic corner cases of the PDDL front end:
;; a deep type hierarchy, `either` types, domain constants, 0-ary predicates,
;; an omitted precondition, an empty conjunction, `imply`, nested quantifiers,
;; a conditional effect that is not inside a `forall`, and a comment ; inside a line.

(define (domain edge-cases)   ; the domain name is folded to lower case
 (:requirements :strips :typing :negative-preconditions :disjunctive-preconditions
                :existential-preconditions :universal-preconditions :conditional-effects
                :equality)
 (:types
   thing - object
   animal plant - thing
   dog cat - animal)
 (:constants rex - dog whiskers - cat fern - plant)
 (:predicates
   (running)
   (happy ?x - animal)
   (owns ?x - (either dog cat) ?y - plant)
   (near ?x ?y - thing))

 ;; no precondition at all: always applicable
 (:action start
   :parameters ()
   :effect (running))

 ;; an empty conjunction as precondition, a conditional effect at the top level
 (:action pet
   :parameters (?a - animal)
   :precondition (and)
   :effect (and (happy ?a)
                (when (near ?a fern) (owns rex fern))))

 (:action inspect
   :parameters (?x - dog ?y - plant)
   :precondition (and (running)
                      (or (happy ?x) (not (near ?x ?y)))
                      (imply (owns ?x ?y) (near ?x ?y))
                      (exists (?z - cat) (forall (?w - plant) (not (owns ?z ?w))))
                      (not (= ?x rex)))
   :effect (and (near ?x ?y) (not (running)))))
