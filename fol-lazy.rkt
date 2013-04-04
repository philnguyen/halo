#lang racket
(require redex "lang.rkt")
(provide P D U E C Theory-T axioms diff gen)

;; translates program into FOL formula
(define-metafunction halo
  P : p -> φ
  [(P [d ...]) (∧* [D d] ...)])

;; translates definition into FOL formula
(define-metafunction halo
  D : d -> φ
  [(D [f x ... = u])
   ([∀ (x ...) (U [f x ...] u)]
    ∧ [∀ (x ...) ([f x ...] = (app* [ptr f] x ...))])])

;; translates RHS into FOL formula
(define-metafunction halo
  U : s u -> φ
  [(U s e) (s = [E e])]
  [(U s [case e (K y ... -> e′) ...])
   (∧* [(t = bad) . ⇒ . (s = bad)]
       [∀ (y ...) ([t = (K y ...)] . ⇒ . [s = (E e′)])] ...
       [(∧* [t . ≠ . bad] [diff t K] ...) . ⇒ . (s = unr)])
   (where t [E e])])

(define-metafunction halo
  diff : t K -> φ
  [(diff t K)
   (t . ≠ . (K [sel K i t] ...))
   (where (i ...) ,(range 0 (arity (term K))))])

;; translates expression into FOL term
(define-metafunction halo
  E : e -> t
  [(E x) x]
  [(E f) (ptr f)]
  [(E [K e ...]) (K [E e] ...)]
  [(E [e_1 e_2]) (app [E e_1] [E e_2])]
  [(E BAD) bad])

;; translates contract satisfaction claim into FOL formula
(define-metafunction halo
  C : e ∈ c -> φ
  [(C e ∈ [flat x e′])
   (∨* [t = unr] [(/ t′ x t) = unr] [(/ t′ x t) = (True)])
   (where (t t′) ([E e] [E e′]))]
  [(C e ∈ ([x : c_1] -> c_2))
   (∀ [x] ([C x ∈ c_1] . ⇒ . [C (e x) ∈ c_2]))]
  [(C e ∈ [c_1 & c_2]) ([C e ∈ c_1] ∧ [C e ∈ c_2])]
  [(C e ∈ CF) (cf [E e])])

(define (Theory-T Ks)
  ;; all constructors are distinct
  (define AxDisjC
    (remove-duplicates
     (for*/list ([Ki Ks] [Ji Ks] #:when (not (equal? Ki Ji)))
       (match-let* ([(list K nK) Ki]
                    [(list J nJ) Ji]
                    [xKs (names 'x nK)]
                    [xJs (names 'y nJ)])
         (if (zero? (+ nK nJ))
             (term ([,K] . ≠ . [,J]))
             (term (∀ (,@ xKs ,@ xJs)
                      ([,K ,@ xKs] . ≠ . [,J ,@ xJs]))))))
     (match-lambda**
      [(`[¬ (,K = ,J)] `[¬ (,J = ,K)]) #t]
      [(`[∀ ,_ (¬ ([,K ,_ ...] = [,J ,_ ...]))]
        `[∀ ,_ (¬ ([,J ,_ ...] = [,K ,_ ...]))]) #t]
      [(_ _) #f])))
  
  ;; constructors and exceptional values are distinct
  (define AxDisjCBU
    (for*/list ([Ki Ks] [t (term (bad unr))])
      (match Ki
        [(list K 0) (term ([,K] . ≠ . ,t))]
        [(list K n) (let ([xs (names 'x n)])
                      (term (∀ ,xs ([,K ,@ xs] . ≠ . ,t))))])))
  
  ;; selector behavior
  (define AxInj
    (for*/list ([Ki Ks] [i (in-range 0 (second Ki))])
      (match-let* ([(list K n) Ki]
                   [xs (names 'x n)])
        (term (∀ ,xs ((sel ,K ,i (,K ,@ xs)) = ,(list-ref xs i)))))))
  
  ;; constructor crash-free ⇔ each field is crash free
  (define AxCfC
    (for/list ([Ki Ks])
      (match Ki
        [(list K 0) (term (cf [,K]))]
        [(list K n) (let ([xs (names 'x n)])
                      (term (∀ ,xs ([cf [,K ,@ xs]]
                                    . ⇔ . [∧* ,@ (for/list ([x xs])
                                                   (term (cf ,x)))]))))])))
  
  (term (∧*
         [∀ (x) ([app bad x] = bad)]
         [∀ (x) ([app unr x] = unr)]
         [bad . ≠ . unr]
         ,@ AxDisjC ,@ AxDisjCBU ,@ AxInj ,@ AxCfC
         (cf unr) (¬ (cf bad)))))

;; returns all axioms generated for program
(define-metafunction halo
  axioms : p -> φ
  [(axioms p) (,[Theory-T Ks] ∧ (P p))])

;; generate assertions from program and contract claim
(define-metafunction halo
  gen : p (e ∈ c) -> {any ...}
  [(gen p [e ∈ c])
   (any_decs ... any_p ... any_¬e∈c ... [check-sat])
   (where {any_decs ...} ,(decs [term p]))
   (where {any_p ...} (z3 (axioms p)))
   (where {any_¬e∈c ...} (z3 (¬ (C e ∈ c))))])