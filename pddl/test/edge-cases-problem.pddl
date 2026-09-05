;; A problem for the edge-cases domain: it declares no objects of its own beyond
;; one extra dog, and uses a purely quantified goal.

(define (problem EdgeCasesProblem)     ; upper case names are folded as well
 (:domain edge-cases)
 (:objects buddy - dog)
 (:init
   (near rex fern)
   (near buddy fern)
   (owns whiskers fern))
 (:goal (and (forall (?a - animal) (happy ?a))
             (exists (?d - dog) (owns ?d fern)))))
