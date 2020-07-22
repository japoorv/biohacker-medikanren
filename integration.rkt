#lang racket
(require math/base)
(require "mediKanren/biolink/pieces-parts/query.rkt") ;; medikanren 
(require "biohacker/BPS/jtms/bms.rkt") ;; bms interface
(require "biohacker/BPS/jtms/logic.rkt") ;; bms utility 


;; common.rkt grab publ. info , subject, object scores, pubmed scores


;;;Utility;;;;

(define (getinfo . lst) ;; prints interval [s s^] for all nodes in lst
  (map tms-node-belief lst))

;;;Particular query 
(define q1 (query/graph ;; changed
                 ((A "UMLS:C0812258") (B "UMLS:C1425762"))
                 ((A->B #f))
                 (A A->B B)))

(define q2 (query/graph ;; no such relation 
                 ((A "UMLS:C0812258") (B #f) )
                 ((A->B #f))
                 (A A->B B)))


;;;Particular query 
(define q3 (query/graph ;; changed
                 ((A "UMLS:C0812258") (B "NCBIGene:7332"))
                 ((A->B #f))
                 (A A->B B)))

(define bms (create-jbms "MediKanren Hook" #:debugging #t #:tolerance 0.0001 #:belief-threshold 0.51))

#|
;; sigmoid function with offset 1000 (assumed avg pubmed counts no reason)
|#

(define (sigmoid_score_calc x) 
  (/ 1 (+ 1 (expt euler.0 (- 1000 x))))
  )

#| score_for_a_concept = average of scores from all publications / 1000
1000 has been assumed to max score based on observations of q3 publication info
|#

(define (concept_score_calc lst)
   (/ (/ (sumlst lst) (length lst)) 1000)    
)

(define (bms-add-node-1-hop query bms symb)
  (define edge (car (edges/query query symb))) ;; edges has publications_info and publications diff ? 
  (define query_subject (edge->subject  edge))
  (define query_object (edge->object edge))
  (define pubmed_counts (pubmed-count edge))
  (define prior (interval 0.75 0.1)) ;; ??
  
  (define subject_score (interval (concept_score_calc (for/list ((x (publications-info-alist-from-edge edge))) (list-ref x 2))) 0.1)) ;; ??
  
  (define object_score (interval (concept_score_calc (for/list ((x (publications-info-alist-from-edge edge))) (list-ref x 3))) 0.1))
  
  (define edge_score (sigmoid_score_calc pubmed_counts))
  
  (define A (tms-create-node bms (concept->curie query_subject) #:belief subject_score)) 
  (define B (tms-create-node bms (concept->curie query_object) #:belief object_score))
  (define -> (tms-create-node bms '-> #:belief (interval edge_score 0.1))) ;; ? s(~A)
  (define A->B (tms-create-node bms 'A->B #:belief (interval 0 0)))
  (justify-node "rtx(A->B)" A->B (list A B ->) prior)
  (displayln (getinfo A->B))
  )

;;(display (report/query q)) ;; gives '((concepts: (A 1) (B 1076)) (edges: (A->B 1556)))

;;(length (remove-duplicates (map edge->subject (edges/query q 'A->B)))) ;; gives 2 why ? though subject 1 


;; Do ranking for multiple 
