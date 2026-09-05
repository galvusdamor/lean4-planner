;; A problem for the transport-lite domain.
;; The plan (load truck pkg loc1) (drive truck loc1 loc2) (unload truck pkg loc2)
;; solves it and has cost 7.

(define (problem deliver-one)
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
 (:metric minimize (total-cost)))
