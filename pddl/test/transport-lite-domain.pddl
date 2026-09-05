;; A small transport-like domain, used as a test case for the PDDL front end.
;; It uses typing, equality, negative preconditions, a universally quantified
;; conditional effect and action costs.

(define (domain transport-lite)
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
   :effect (and (not (in ?p ?v)) (at ?p ?l) (increase (total-cost) 1))))
