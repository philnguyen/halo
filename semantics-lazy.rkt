#lang racket
(require redex "lang.rkt")
(provide (all-defined-out))

;; environment functions
(define ∅ (λ (x) (error "out of domain:" x)))
(define ++
  (match-lambda**
   [(ρ [list x ...] [list d ...])
    (for/fold ([ρ ρ]) ([x x] [d d]) (++ ρ x d))]
   [(ρ x d) (λ (z) (if (equal? x z) d (ρ z)))]))

;; semantics object D is one of:
;; - (list K D^n)
;; - (D -> D)
;; - Bad
;; - ⊥

;; E : (FunVar -> D) (Var -> D) -> D
(define (E e σ ρ)
  (match e
    ['BAD 'Bad]
    [(? symbol? x) (ρ x)]
    [`(F ,f) (σ f)]
    [`(,[? K? K] ,e ...) `(,K ,@ (for/list ([ei e]) (E ei σ ρ)))]
    [`(,e1 ,e2) (App [E e1 σ ρ] [E e2 σ ρ])]))

;; U : u (FunVar -> D) (Var -> D) -> D
(define (U u σ ρ)
  (match u
    [`(case ,e ,alts ...)
     (match [E e σ ρ]
       [`(,K ,d ...) (for/first ([alt alts] #:when
                                            (match-let ([`(,Ki ,_ ...) alt])
                                              (equal? Ki K)))
                       (match-let ([`(,K ,y ... -> ,e′) alt])
                         (E e′ σ [++ ρ y d])))]
       ['Bad 'Bad]
       [_ '⊥])]
    [e (E e σ ρ)]))

;; P : p (FunVar -> D) -> FunVar -> D
(define (P p σ)
  
  (define (mk-fn xs u ρ)
    (match xs
      ['() (U u σ ρ)]
      [(cons x zs) (λ (d) (mk-fn zs u [++ ρ x d]))]))
  
  (λ (f)
    (or (for/or ([d p])
          (match-let ([`([F ,fi] ,x ... = ,u) d])
            (cond
              [(equal? fi f) (mk-fn x u ∅)]
              [else #f])))
        '⊥)))

;; PP : p -> FunVar -> D
(define (PP p)
  (define (σ f) ((P p σ) f))
  σ)

;; App : D D -> D
(define App
  (match-lambda**
   [([? procedure? f] x) (f x)]
   [('Bad _) 'Bad]
   [(_ _) '⊥]))