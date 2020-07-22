#lang racket
(require math/base)
(require "../mediKanren/biolink/pieces-parts/query.rkt") ;; medikanren 
(require "../biohacker/BPS/jtms/bms.rkt") ;; bms interface
(require "../biohacker/BPS/jtms/logic.rkt") ;; bms utility


;;;Utility;;;;

(define (getinfo . lst) ;; prints interval [s s^] for all nodes in lst
  (map tms-node-belief lst))

(define (negated? edge) ;; checking whether edge is negated or not
  (define neg (string-downcase (cdr (assoc "negated" (edge->props edge)))))
  (equal? neg "true")
  )

;;;;;Queries;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;
(define q2 (query/graph ;; for all relations from A to any B  
                 ((A "UMLS:C0812258") (B #f) )
                 ((A->B #f))
                 (A A->B B)))


;;;Particular query Single hop
(define q3 (query/graph ;; changed
                 ((A "UMLS:C0812258") (B "NCBIGene:7332"))
                 ((A->B #f))
                 (A A->B B)))

(define q3a (query/graph ;; Gives two edges between B 
                 ((A "UMLS:C0812258") (B "CUI:C0001418"))
                 ((A->B #f))
                 (A A->B B)))

;;;Particular query Two Hop 
(define q4 (query/graph
                 ((A "UMLS:C0812258") (X #f)(B "NCBIGene:7332"))
                 ((A->X #f) (X->B #f))
                 (A A->X X X->B B)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;BMS Utilities;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|
;; sigmoid function with offset 0 (used for edge scoring)
|#

(define (sigmoid-score-calc x) 
  (/ 1 (+ 1 (expt euler.0 (- 0 x))))
  )

#| score-for-concept = average of scores from all publications / 1000
|#

(define (score-for-concept lst)
  (cond
    ((empty? lst) 0) ;; Score 0 for no publications
    (else  (/ (/ (sumlst lst) (length lst)) 1000))
    )
  )

#| For calculating belief of concept given :
 list of concept scores from publication info
 concept type (subject/object)
 negated? : edge negated or not

|#
(define (concept-belief-calc lst symbol neg?)
  (cond
    (neg? (interval 0 (score-for-concept lst)))
    (else (interval (score-for-concept lst) 0))
  )
)
#| Function for calculating the edge belief 
|#
(define (edge-belief-calc pubmed-counts neg?)
  (cond
    (neg? (interval 0 (sigmoid-score-calc pubmed-counts)))
    (else (interval (sigmoid-score-calc pubmed-counts) 0))
    )
  )

(define (split-predicate predicates)
  (list positively-regulates predicates)
  )


#| There can be multiple curie names refering to the same concept. 
   We call these synonym curies hence they belong to a single equivalence class.
   (get-representative <curie-name>) gives the representative curie-name for that equivalence class.
|#
(define (get-representative curie) ;; first curie after sorting (lexically) the equivalence class
  (car (sort (set->list (curie-synonyms curie)) string<=?))
  )

#| Utility for giving a unique name for the edge in KB
|#
(define (edge->bms-node-name edge)
  (define subject-curie (get-representative (concept->curie (edge->subject edge))))
  (define object-curie (get-representative (concept->curie (edge->object edge))))
  (define predicate (cdr (edge->pred edge)))
  (define negated (cdr (assoc "negated" (edge->props edge))))
  (string-append negated "-" subject-curie "-" predicate "-" object-curie)
  )
#|
 Converts a KB edge to a bms node with belief interval (Support(node), Support(not node)) using (A and B and ->)  for A->B
|#
(define (edge->bms-node edge bms) 
  (define query_subject (edge->subject  edge))
  (define query_object (edge->object edge))
  (define pubmed_counts (pubmed-count edge))
  (define prior (interval 1 0)) ;; ??
  (define subject-belief (concept-belief-calc (for/list ((x (publications-info-alist-from-edge edge))) (list-ref x 2)) 'subject (negated? edge)))
  (define object-belief (concept-belief-calc (for/list ((x (publications-info-alist-from-edge edge))) (list-ref x 3)) 'object (negated? edge)))
  (define edge-belief (edge-belief-calc pubmed_counts (negated? edge)))
  (define A subject-belief) 
  (define B  object-belief)
  (define -> edge-belief) ;; ? s(~A)
  (define node-support (impli (andi (list A B ->)) prior))
  (tms-create-node bms (edge->bms-node-name edge) #:belief node-support)
  )

;; 1 Hop + 2 Hop 

(define (bms-add-node curieA curieB predicates bms)
  (define query (query/graph
                  ((A curieA) (B curieB))
                  ((A->B predicates))
                  (A A->B B)))
  
  (define A->B (tms-create-node bms 'A->B #:belief (interval 0 0)))
  (for ((edge (edges/query query 'A->B)))
    (begin 
      (define query_subject (edge->subject  edge))
      (define query_object (edge->object edge))
      (define pubmed_counts (pubmed-count edge))
      (define prior (interval 1 0)) ;; ??
     
      (define subject_score (concept-belief-calc (for/list ((x (publications-info-alist-from-edge edge))) (list-ref x 2)) 'subject (negated? edge))) 
      
      (define object_score (concept-belief-calc (for/list ((x (publications-info-alist-from-edge edge))) (list-ref x 3)) 'object (negated? edge)))
      
      (define edge_score (edge-belief-calc pubmed_counts (negated? edge)))
      
      (define A (tms-create-node bms (concept->curie query_subject) #:belief subject_score)) 
      (define B (tms-create-node bms (concept->curie query_object) #:belief object_score))
      (define -> (tms-create-node bms '-> #:belief edge_score)) ;; ? s(~A)
      (justify-node (gensym (cdr (edge->pred edge))) A->B (list A B ->) prior)
      (displayln (getinfo A->B))
      )
    )

  ;;2 HOP
   (define prior (interval 1 0)) ;; Suitable Prior ?
   (match-define (list lst1 lst2) (split-predicate predicates))
   (define query-2hop (query/graph
                  ((A curieA) (X #f)  (B curieB))
                  ((A->X lst1) (X->B lst2))
                  (A A->X X X->B B)))
  (define object-hash (make-hash)) ;; (X_curie,list of all edges A->X)
  (define subject-hash (make-hash)) ;; (X_curie,list of all edges X->B)

  (for ((edge (edges/query query-2hop 'A->X)))
    (begin
      (define X-name (get-representative (concept->curie (edge->object edge)))) ;; get-representative define above
      (define hash-val (hash-ref! object-hash X-name '()))
      (hash-set! object-hash X-name (cons (edge->bms-node edge bms) hash-val))
      )
    )

   (for ((edge (edges/query query-2hop 'X->B)))
    (begin
      (define X-name (get-representative (concept->curie (edge->subject edge))))
      (define hash-val (hash-ref! subject-hash X-name '()))
      (hash-set! subject-hash X-name (cons (edge->bms-node edge bms) hash-val))
      )
    )

  (for ((X-name (hash-keys object-hash)))
      (begin
        (for ((A->X (hash-ref! object-hash X-name '())))
          (begin
            (for ((X->B (hash-ref! subject-hash X-name '())))
              (begin
                (justify-node (gensym X-name) A->B (list A->X X->B) prior)
               ;; (displayln (list A->X X->B A->B)) 
                )
              )
            )
          )
        )
      )
  (displayln (getinfo A->B))
  )


 

#|
;; TODO Apoorv
4) Support against 0 if no negated edge
5) Different way to combine the edges A->X, X->B 
6) Various cases : 1 Hop, 2 Hop, A->X, X->B 
8) Negated edges should be used for s(~A)
9) (two-hop curieA X curieB predicate1 predicate2 bms) 
|#

;; S ---treats--->X---causes---> O
;;imatinib CUI:C0939537
;;ashthma CUI:C0004096
;; eosinophilia      CUI:C0014457
