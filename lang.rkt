#lang racket
(require redex)
(provide (all-defined-out))

(define-language halo
  ; haskell
  [p (d ...)]
  [d (f x ... = u)]
  [u e (case e [K y ... -> e] ...)]
  [(e e′) x f (K e ...) (e e) BAD]
  [c (flat x e) ([x : c] -> c) (c & c) CF]
  
  ; FOL
  [(s t t′) x (f t ...) (K t ...) (sel K i t) (ptr f) (app t s) unr bad]
  [(φ ψ) (cf t) (t = t) (φ ∧ φ) (φ ∨ φ) (¬ φ) (∀ (x ...) φ) (∃ (x ...) φ)]
  
  [f (F x_name)]
  [(K J) True False Succ Zero Cons Nil]
  [i natural]
  [(x y z) variable-not-otherwise-mentioned])

(define K? (redex-match? halo K))

;; substitute x/t1 in t
(define-metafunction halo
  / : t x t_1 -> t
  [(/ x x t) t]
  [(/ x z t) x]
  [(/ (f t ...) x t_1) (f [/ t x t_1] ...)]
  [(/ (K t ...) x t_1) (K [/ t x t_1] ...)]
  [(/ (sel K i t) x t_1) (sel K i [/ t x t_1])]
  [(/ (ptr f) x t_1) (ptr f)]
  [(/ (app t ...) x t_1) (app [/ t x t_1] ...)]
  [(/ unr x t) unr]
  [(/ bad x t) bad])

;;;;; CONVENIENT MACROS

;; big conjunction
(define-metafunction halo
  ∧* : φ φ ... -> φ
  [(∧* φ) φ]
  [(∧* φ ψ ...) (φ ∧ [∧* ψ ...])])

;; big disjunction
(define-metafunction halo
  ∨* : φ φ ... -> φ
  [(∨* φ) φ]
  [(∨* φ ψ ...) (φ ∨ [∨* ψ ...])])

;; curry application
(define-metafunction halo
  app* : t ... -> t
  [(app* t) t]
  [(app* t_f t_x t_y ...) (app* [app t_f t_x] t_y ...)])
(define-metafunction halo
  @ : e ... -> e
  [(@ e) e]
  [(@ e_1 e_2 e_3 ...) (@ [e_1 e_2] e_3 ...)])

;; desugar implication
(define-metafunction halo
  ⇒ : φ φ -> φ
  [(φ . ⇒ . ψ) ([¬ φ] ∨ ψ)])

;; desugar equivalence
(define-metafunction halo
  ⇔ : φ φ -> φ
  [(φ . ⇔ . ψ) ([φ . ⇒ . ψ] ∧ [ψ . ⇒ . ψ])])

;; desugar difference
(define-metafunction halo
  ≠ : t t -> φ
  [(s . ≠ . t) (¬ [s = t])])

;; primitive constructors
(define Ks
  ;; (constructor × arity) pairs, default arity 0
  (for/list ([p (term {True False (Cons 2) Nil Zero (Succ 1)})])
    (match p
      [(? symbol? K) (list K 0)]
      [_ p])))

(define (arity K)
  (second (assoc K Ks)))

;; generates n (distinc) symbols with given prefix
(define (names x n)
  (variables-not-in x (make-list n x)))

;;;;; generate input for Z3
(define (decs p)
  `([declare-sort T]
    
    ; declare function constants
    ,@ (for/list ([d p])
         (match-let* ([`([F ,f] ,x ... = ,u) d]
                      [const-f (prefx 'f f)])
           (match (length x)
             [0 `(declare-const ,const-f T)]
             [n `(declare-fun ,const-f ,(make-list n 'T) T)])))
    ; declare function pointers
    ,@ (for/list ([d p])
         (match-let ([`([F ,f] ,x ... = ,u) d])
           `(declare-const ,(prefx 'ptr f) T)))
    ; declare constructors
    ,@ (for/list ([k Ks])
         (match k
           [(list K 0) `(declare-const ,(prefx 'k K) T)]
           [(list K n) `(declare-fun ,(prefx 'k K) ,(make-list n 'T) T)]))
    ; declare selectors
    ,@ (for*/list ([k Ks] [n (in-value [second k])] [i (in-range 0 n)])
         `(declare-fun
           ,(prefx (string->symbol (string-append "sel-" (number->string i)))
                   (first k))
           (T) T))
    ; declare app
    [declare-fun app (T T) T]
    [declare-const unr T]
    [declare-const bad T]
    [declare-fun cf (T) Bool]))

(define (prefx x y)
  (string->symbol (string-append (symbol->string x) "-" (symbol->string y))))

;; generate z3 assertions from formula
(define-metafunction halo
  z3 : φ -> (any ...)
  [(z3 (φ ∧ ψ))
   (any_1 ... any_2 ...)
   (where (any_1 ...) (z3 φ)) (where (any_2 ...) (z3 ψ))]
  [(z3 φ) {(assert [z3-φ φ])}])

;; convert formula
(define-metafunction halo
  z3-φ : φ -> any
  [(z3-φ (cf t)) (cf [z3-t t])]
  [(z3-φ (t_1 = t_2)) (= [z3-t t_1] [z3-t t_2])]
  [(z3-φ (φ ∧ ψ)) (and [z3-φ φ] [z3-φ ψ])]
  [(z3-φ ([¬ φ] ∨ ψ)) (implies [z3-φ φ] [z3-φ ψ])]
  [(z3-φ (φ ∨ ψ)) (or [z3-φ φ] [z3-φ ψ])]
  [(z3-φ (φ ⇒ ψ)) (implies [z3-φ φ] [z3-φ ψ])]
  [(z3-φ (¬ φ)) (not [z3-φ φ])]
  [(z3-φ (∀ () φ)) (z3-φ φ)]
  [(z3-φ (∀ (x ...) φ)) (forall ([x T] ...) [z3-φ φ])]
  [(z3-φ (∃ () φ)) [z3-φ φ]]
  [(z3-φ (∃ (x ...) φ)) (exists ([x T] ...) [z3-φ φ])])

;; convert term
(define-metafunction halo
  z3-t : t -> any
  [(z3-t x) x]
  [(z3-t ([F x])) ,(prefx 'f [term x])]
  [(z3-t ([F x] t ...)) (,(prefx 'f [term x]) [z3-t t] ...)]
  [(z3-t (K)) ,(prefx 'k [term K])]
  [(z3-t (K t ...)) (,(prefx 'k [term K]) [z3-t t] ...)]
  [(z3-t (sel K i t))
   (,[prefx (string->symbol (string-append "sel-" (number->string [term i])))
            (term K)]
    [z3-t t])]
  [(z3-t (ptr [F x])) ,(prefx 'ptr [term x])]
  [(z3-t (app t s)) (app [z3-t t] [z3-t s])]
  [(z3-t unr) unr]
  [(z3-t bad) bad])

;;;;; Example program
(define p
  (term
   (#;[(F not) x = (case x
                     [True -> (False)]
                     [False -> (True)])]
    #;[(F even?) n = (case n
                       [Zero -> (True)]
                       [Succ m -> ([F not] ([F even?] m))])]
    [(F nil?) x = (case x
                    [Nil -> (True)]
                    [Cons z zs -> (False)])]
    [(F map) f xs = (case xs
                      [Nil -> (Nil)]
                      [Cons z zs -> (Cons [f z] [@ (F map) f zs])])])))