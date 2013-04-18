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
  [(φ ψ) (cf t) (= t t) (≠ t t)
         (∧ φ ...) (∨ φ ...) (¬ φ) (⇒ φ φ) (⇔ φ φ)
         (∀ (x ...) φ) (∃ (x ...) φ)]
  
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

;; explicitly rename recusrive call
(define-metafunction halo
  ann-rec : u x -> u
  [(ann-rec (case e [K y ... -> e_K] ...) x)
   (case [ann-rec e x] [K y ... -> (ann-rec e_K x)] ...)]
  [(ann-rec x z) x]
  [(ann-rec (F x) x) (F ,(prefx 'rec [term x]))]
  [(ann-rec (F z) x) (F z)]
  [(ann-rec (K e ...) x) (K [ann-rec e x] ...)]
  [(ann-rec (e_1 e_2) x) ([ann-rec e_1 x] [ann-rec e_2 x])]
  [(ann-rec BAD x) BAD])

;;;;; CONVENIENT MACROS

;; multiple-argument function contract
(define-metafunction halo
  ->* : (x : c) (x : c) ... c -> ([x : c] -> c)
  [([x : c_x] . ->* . c_y) ([x : c_x] -> c_y)]
  [([x : c_x] [y : c_y] ... . ->* . c_z)
   ([x : c_x] -> ([y : c_y] ... . ->* . c_z))])

;; curry application
(define-metafunction halo
  app* : t ... -> t
  [(app* t) t]
  [(app* t_f t_x t_y ...) (app* [app t_f t_x] t_y ...)])
(define-metafunction halo
  @ : e ... -> e
  [(@ e) e]
  [(@ e_1 e_2 e_3 ...) (@ [e_1 e_2] e_3 ...)])

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
    ,@ (for/fold ([acc empty]) ([d p])
         (match-let* ([`([F ,f] ,x ... = ,u) d]
                      [n (length x)])
           (append (list `[declare-fun ,(prefx 'f f) ,(make-list n 'T) T]
                         `[declare-fun ,(prefx 'rec f) ,(make-list n 'T) T]
                         `[declare-const ,(prefx 'ptr f) T]
                         `[declare-const ,(prefx 'ptr-rec f) T])
                   acc)))
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
  z3 : φ -> ((assert any) ...)
  #;[(z3 (∀ (x ...) (⇔ φ (∧ ψ ...))))
     (any_1 ... any_2 ...)
     (where (any_1 ...) ((z3 (∀ (x ...) (⇒ φ ψ))) ...))
     (where (any_2 ...) (z3 (∀ (x ...) (⇒ (∧ ψ ...) φ))))]
  [(z3 (∀ (x ...) (∧ φ ...))) (@@ (z3 (∀ (x ...) φ)) ...)]
  [(z3 (∧ φ ...)) (@@ (z3 φ) ...)]
  [(z3 φ) {(assert [z3-φ φ])}])

(define-metafunction halo
  @@ : {any ...} ... -> {any ...}
  [(@@ {any ...} ...) {any ... ...}])

;; convert formula
(define-metafunction halo
  z3-φ : φ -> any
  [(z3-φ (cf t)) (cf [z3-t t])]
  [(z3-φ (= s t)) (= [z3-t s] [z3-t t])]
  [(z3-φ (≠ s t)) (distinct [z3-t s] [z3-t t])]
  [(z3-φ (∧ φ)) (z3-φ φ)]
  [(z3-φ (∧ φ ...)) (and [z3-φ φ] ...)]
  [(z3-φ (∨ φ)) (z3-φ φ)]
  [(z3-φ (∨ φ ...)) (or [z3-φ φ] ...)]
  [(z3-φ (¬ φ)) (not [z3-φ φ])]
  [(z3-φ (⇒ φ ψ)) (=> [z3-φ φ] [z3-φ ψ])]
  [(z3-φ (⇔ φ ψ)) (= [z3-φ φ] [z3-φ ψ])]
  [(z3-φ (∀ (x ...) (∀ (z ...) φ))) (z3-φ (∀ (x ... z ...) φ))]
  [(z3-φ (∀ () φ)) (z3-φ φ)]
  [(z3-φ (∀ (x ...) φ)) (forall ([x T] ...) [z3-φ φ])]
  [(z3-φ (∃ (x ...) (∃ (z ...) φ))) (z3-φ (∃ (x ... z ...) φ))]
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
   ([(F cons?) xs = (case xs
                      [Nil -> (False)]
                      [True -> (True)])]
    
    ;; higher order list functions
    [(F foldr) f a xs = (case xs
                          [Nil -> a]
                          [Cons z zs -> (@ f z (@ [F foldr] f a zs))])]
    [(F foldl) f a xs = (case xs
                          [Nil -> a]
                          [Cons z zs -> (@ [F foldl] f (@ f a z) zs)])]
    [(F map) f xs = (@ [F foldr] ([F map-foldr-step] f) (Nil) xs)]
    [(F map-foldr-step) f x ys = (Cons (f x) ys)]
    [(F reverse) xs = (@ [F foldl] [F cons-eta] (Nil) xs)]
    [(F cons-eta) x xs = (Cons x xs)]
    
    ;; partial functions
    [(F head) xs = (case xs
                     [Nil -> BAD]
                     [Cons z zs -> z])]
    [(F tail) xs = (case xs
                     [Nil -> BAD]
                     [Cons z zs -> zs])]
    [(F foldr1) f xs = (@ [F foldr] f ([F head] xs) ([F tail] xs))])))