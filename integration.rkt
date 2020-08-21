  #lang racket
  (require math/base)
  (require "../mediKanren/biolink/pieces-parts/query.rkt") ;; medikanren 
  (require "../biohacker/BPS/jtms/bms.rkt") ;; bms interface
  (require "../biohacker/BPS/jtms/logic.rkt") ;; bms utility

;;;Usage;;;;
#|
1) Ranking :
1.1) First create a jbms (Justification based Belief Maint. System)
     (define bms (create-jbms "Simple"))

1.2) (pretty-print (rank-2-hop "UMLS:C0812258" "NCBIGene:7332" #f bms))
     (pretty-print (rank-1-hop "UMLS:C0812258" positively-regulates 'subject bms))

2) Getting overall belief in a node A->B

2.1) 1 Hop (bms-add-node-1-hop curieA curieB predicates bms)
2.2) 1 Hop + 2 Hop (bms-add-node curieA curieB predicates bms)
2.3) 1 Hop + 2 Hop .... n Hop (bms-add-node-n-hop curieA curieB predicates hops bms)
    
|#


  ;;;Utility;;;;

  (define (getinfo . lst) ;; prints interval [s s^] for all nodes in lst
    (map tms-node-belief lst))

  (define (negated-edge edge)
    (let ((a (assoc "negated" (edge->props edge))))
      (if a
          (cdr a)
          "false")))

  (define (negated? edge) ;; checking whether edge is negated or not
    (define neg (string-downcase (negated-edge edge)))
    (equal? neg "true")
    )
  (define (score i1) ;; given a [s(A),s(~A)] find the score for the confidence 
    (/ (+ (interval-s i1) (- 1 (interval-p i1))) 2)
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

  #| Utility for giving a unique name for the edge  in KB
  |#
  (define (edge->bms-node-name edge)
    (define subject-curie (get-representative (concept->curie (edge->subject edge))))
    (define object-curie (get-representative (concept->curie (edge->object edge))))
    (define predicate (cdr (edge->pred edge)))
    (define negated (negated-edge edge))
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


 #|
 Given (curieA curieB predicates) below function returns the bms-node A->B with belief coming from a single hop only ie curieA,curieB, relation between them 
 |#
  (define (bms-add-node-1-hop curieA curieB predicates bms) ;; predicates a list
    (define query (query/graph
                    ((A curieA) (B curieB))
                    ((A->B predicates))
                    (A A->B B)))

    (define A->B (tms-create-node bms 'A->B #:belief (interval 0 0)))
    (define antes-list (for/list ((edge (edges/query query 'A->B))) (edge->bms-node edge bms)))
    (define prior (interval 1 0)) ;; Suitable Prior ?
    (justify-node (gensym) A->B antes-list prior)
    A->B
    )
  ;; Returns the node A->B with the belief propogated using both 1 Hop, 2 Hop

  (define (bms-add-node curieA curieB predicates bms) ;; predicates a list
    (define query (query/graph
                    ((A curieA) (B curieB))
                    ((A->B predicates))
                    (A A->B B)))

    (define A->B (tms-create-node bms 'A->B #:belief (interval 0 0)))
    (define antes-list (for/list ((edge (edges/query query 'A->B))) (edge->bms-node edge bms)))
    (define prior (interval 1 0)) ;; Suitable Prior ?
    (justify-node (gensym) A->B antes-list prior)
    ;;2 HOP
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
        (define hash-val (hash-ref object-hash X-name '()))
        (hash-set! object-hash X-name (cons (edge->bms-node edge bms) hash-val))
        )
      )

     (for ((edge (edges/query query-2hop 'X->B)))
      (begin
        (define X-name (get-representative (concept->curie (edge->subject edge))))
        (define hash-val (hash-ref subject-hash X-name '()))
        (hash-set! subject-hash X-name (cons (edge->bms-node edge bms) hash-val))
        )
      )

    (for ((X-name (hash-keys object-hash)))
        (begin
         (define object-list (for/list ((x (hash-ref  object-hash X-name '()))) x)) 
         (define subject-list (for/list ((x (hash-ref subject-hash X-name '()))) x))
         (define A->X (tms-create-node bms (gensym) #:belief (interval 0 0)))
         (define X->B (tms-create-node bms (gensym) #:belief (interval 0 0)))
         (justify-node 'A->X A->X object-list prior)
         (justify-node 'X->B X->B subject-list prior)
         (justify-node 'A->B A->B (list A->X X->B) prior)
         )
        )
    (displayln (getinfo A->B))
    )

 #|
 Return a bms node corrosponding to (A->B predicates) including n hops between A->B
The belief is a culmination of all hops from 1 to n 
 |#
 (define (bms-add-node-n-hop curieA curieB predicates hops bms)
     (cond
        ((> 1 hops) (error "Hops need to be atleast 1"))
        ((= 1 hops) (bms-add-node-1-hop curieA curieB predicates bms))
        (else
         (begin
           (define prior (interval 1 0))
           (define A->B (tms-create-node bms 'A->B #:belief (interval 0 0)))
           (define q1
             (query/graph
              ((A curieA) (B curieB))
              ((A->B predicates))
              (A A->B B)))
           (match-define (list lst1 lst2) (split-predicate predicates))
           (define q2 ;; For splitting to A->X X->B
             (query/graph
              ((A curieA) (X #f) (B curieB))
              ((A->X lst1) (X->B lst2))
              (A A->X X X->B B)))
           (define antes-lst (for/list ((edges (edges/query q1 'A->B))) (edge->bms-node edges bms)) )
           (justify-node (gensym) A->B antes-lst prior)
           (define object-hash (make-hash)) ;; (X_curie,list of all edges A->X)
           (define subject-hash (make-hash)) ;; (X_curie,list of all edges X->B)
           (for ((edge (edges/query q2 'A->X)))
             (begin
               (define X-name (get-representative (concept->curie (edge->object edge))))
               (define hash-val (hash-ref object-hash X-name '()))
               (when (empty? hash-val) (hash-set! object-hash X-name  (bms-add-node-n-hop curieA X-name lst1 (- hops 1) bms) ))
               )
             )
           (for ((edge (edges/query q2 'X->B)))
             (begin
               (define X-name (get-representative (concept->curie (edge->subject edge))))
               (define hash-val (hash-ref subject-hash X-name '()))
               (hash-set! subject-hash X-name (cons (edge->bms-node edge bms) hash-val))
               )
             )
     (for ((X-name (hash-keys object-hash)))
         (begin
           (define def  (tms-create-node bms (gensym) #:belief (interval 0 0)))
           (define A->X (hash-ref object-hash X-name def))
           (define subject-list (for/list ((x (hash-ref subject-hash X-name '()))) x))
           (define X->B (tms-create-node bms 'X->B #:belief (interval 0 0)))
           (justify-node 'X->B X->B subject-list prior)
           (justify-node 'A->B A->B (list A->X X->B) prior)
          )
         )
     A->B
           )
         )
        )
      )

 #|
 For sorting the A->X->B paths on the basis of their support for A->B 
 For scoring the A->X->B score is used ,which has following signature score = interval -> number (real number in [0 1])
 |#
 (define (rank-2-hop curieA curieB predicates bms)
   (match-define (list lst1 lst2) (split-predicate predicates))
   (define q1 (query/graph ((A curieA) (X #f) (B curieB))
                           ((A->X lst1) (X->B lst2))
                           (A A->X X X->B B)))
    (define object-hash (make-hash)) ;; (X_curie,list of all edges A->X)
    (define subject-hash (make-hash)) ;; (X_curie,list of all edges X->B)

    (for ((edge (edges/query q1 'A->X)))
      (begin
        (define X-name (get-representative (concept->curie (edge->object edge)))) ;; get-representative define above
        (define hash-val (hash-ref object-hash X-name '()))
        (hash-set! object-hash X-name (cons (edge->bms-node edge bms) hash-val))
        )
      )

     (for ((edge (edges/query q1 'X->B)))
      (begin
        (define X-name (get-representative (concept->curie (edge->subject edge))))
        (define hash-val (hash-ref subject-hash X-name '()))
        (hash-set! subject-hash X-name (cons (edge->bms-node edge bms) hash-val))
        )
      )
    (define prior (interval 1 0))
    (define ranked-hash (make-hash))
    (for ((X-name (hash-keys object-hash)))
         (begin
          (define object-list (for/list ((x (hash-ref  object-hash X-name '()))) x)) 
          (define subject-list (for/list ((x (hash-ref subject-hash X-name '()))) x))
          (define A->X (tms-create-node bms (gensym) #:belief (interval 0 0)))
          (define X->B (tms-create-node bms (gensym) #:belief (interval 0 0)))
          (justify-node 'A->X A->X object-list prior)
          (justify-node 'X->B X->B subject-list prior)
          (define temp (tms-create-node bms 'temp #:belief (interval 0 0)))
          (justify-node 'temp temp (list A->X X->B) prior)
          (hash-set! ranked-hash X-name (score (tms-node-belief temp)))
          )
         )
   (define (comp x y)
     (> (cdr x) (cdr y))
     )
    (sort (hash->list ranked-hash) comp)
   )


;;; Gives the ranking of 1 hop from X->B or A->X by mentioning concept-type-predicate as 'subject for A->X and 'object otherwise
 (define (rank-1-hop curie predicates concept-type-provided bms)
   (define query #f) ;; The query as per the concept-type-provided
   (define symb_edge #f) ;; X->B, A->X
   (define curie-extractor #f) ;; for extracting object/subject from edge
   (define prior (interval 1 0))
   (cond
     ((equal? concept-type-provided 'subject)
        (set! query (query/graph ((A curie) (X #f))
                                 ((A->X predicates))
                                 (A A->X X)))
        (set! symb_edge 'A->X)
        (set! curie-extractor edge->object)
        )
     (else 
        (set! query (query/graph ((X #f) (B curie))
                                 ((X->B predicates))
                                 (X X->B B)))
        (set! symb_edge 'X->B)
        (set! curie-extractor edge->subject)
        )
     )
   (define concept-hash (make-hash))
    (for ((edge (edges/query query symb_edge)))
      (begin
        (define X-name (get-representative (concept->curie (curie-extractor edge))))
        (define hash-val (hash-ref concept-hash X-name '()))
        (hash-set! concept-hash X-name (cons (edge->bms-node edge bms) hash-val))
        )
      )
   (define ranked-hash (make-hash))
   (for ((X-name (hash-keys concept-hash)))
     (begin
       (define lst-concept (for/list ((x (hash-ref concept-hash X-name '()))) x))
       (define temp (tms-create-node bms 'temp #:belief (interval 0 0)))
       (justify-node 'temp temp lst-concept prior)
       (hash-set! ranked-hash X-name (score (tms-node-belief temp)))
      )
     )
    (define (comp x y)
     (> (cdr x) (cdr y))
     )
    (sort (hash->list ranked-hash) comp)
   )

 (define bms (create-jbms "Simple"))
 ;;(pretty-print (time (bms-add-node-n-hop "UMLS:C0812258" "NCBIGene:7332" #f 2 bms))) 
 ;;(pretty-print (time (bms-add-node-n-hop "UMLS:C0812258" "NCBIGene:7332" #f 3 bms))) ;; 400 seconds

 (pretty-print (rank-2-hop "UMLS:C0812258" "NCBIGene:7332" #f bms))
 (set! bms (create-jbms "Simple"))
 (pretty-print (rank-1-hop "UMLS:C0812258" positively-regulates 'subject bms))
 (set! bms (create-jbms "Simple"))
 (pretty-print (rank-1-hop "NCBIGene:7332" positively-regulates 'object bms))


#|
  ;; S ---treats--->X---causes---> O
  ;;imatinib CUI:C0939537
  ;;ashthma CUI:C0004096
 ;; eosinophilia      CUI:C0014457
 |# 


#|

Concerns: 
2) What about upregulates and downregulates
3) Meta-rule adjusting for feedbacks

|#
