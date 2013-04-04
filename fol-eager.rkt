#lang racket
(require
 redex "lang.rkt"
 (only-in "fol-lazy.rkt" [P P′] E C diff [axioms axioms′] [gen gen′]))
(provide P D U E C Theory-T axioms diff gen)

(define-extended-language halo′ halo)

;; translates program into FOL formula
(define-metafunction halo′
  P : p -> φ
  [(P [d ...]) (∧* [D d] ...)])

;; translates definition into FOL formula
(define-metafunction halo′
  D : d -> φ
  [(D [f x ... = u])
   ([∀ (x ...) ((∧* [OK x] ...) . ⇒ . [U (f x ...) u])]
    ∧ [∀ (x ...) ([f x ...] = [app* (ptr f) x ...])])])

(define-metafunction halo′
  OK : t -> φ
  [(OK t) ([t . ≠ . bad] ∧ [t . ≠ . unr])])

;; translates RHS into FOL formula
(define-metafunction halo′
  U : s u -> φ
  [(U s e) (s = [E e])]
  [(U s [case e (K y ... -> e′) ...])
   (∧* [(t = bad) . ⇒ . (s = bad)]
       [∀ (y ...) (([OK t] ∧ [t = (K y ...)]) . ⇒ . [s = (E e′)])] ...
       [(∧* [t . ≠ . bad] [diff t K] ...) . ⇒ . (s = unr)])
   (where t (E e))])

(define (Theory-T Ks)
  (define (X i) (string->symbol (string-append "x" (number->string i))))
  
  ;; all constructors are distinct if they don't fail or diverge
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
                      ([(OK [,K ,@ xKs]) ∧ (OK [,J ,@ xJs])]
                       . ⇒ . ([,K ,@ xKs] . ≠ . [,J ,@ xJs])))))))
     (match-lambda**
      [(`[¬ (,K = ,J)] `[¬ (,J = ,K)]) #t]
      [(`[∀ ,_ (,_ ∨ (¬ ([,K ,_ ...] = [,J ,_ ...])))]
        `[∀ ,_ (,_ ∨ (¬ ([,J ,_ ...] = [,K ,_ ...])))]) #t]
      [(_ _) #f])))
  
  ;; constructor maps value to non-exceptional values if all
  ;; the fields 'behave'
  (define AxDisjCBU
    (for*/list ([Ki Ks] [t (term (bad unr))])
      (match Ki
        [(list K 0) (term ([,K] . ≠ . ,t))]
        [(list K n)
         (let ([xs (map X (range 0 n))])
           (term
            (∀ ,xs
               ((∨*
                 ,@ (for/list ([i (in-range 0 n)])
                      (for/fold ([φ (term (,[X i] = ,t))]) ([j (in-range 0 i)])
                        (term (,φ ∧ (,[X j] . ≠ . ,(first (remove t '(bad unr)))))))))
                . ⇔ . [(,K ,@ xs) = ,t]))))])))
  
  ;; selector behavior
  (define AxInj
    (for*/list ([Ki Ks] [i (in-range 0 (second Ki))])
      (match-let* ([(list K n) Ki]
                   [xs (names 'x n)])
        (term (∧*
               (∀ ,xs ((∧* ,@ (for/list ([x xs]) (term (OK ,x))))
                       . ⇒ .((sel ,K ,i (,K ,@ xs)) = ,(list-ref xs i))))
               (∀ ,xs (([,K ,@ xs] = bad) . ⇔ . ((sel ,K ,i (,K ,@ xs)) = bad)))
               (∀ ,xs (([,K ,@ xs] = unr) . ⇔ . ((sel ,K ,i (,K ,@ xs)) = unr))))))))
  
  ;; crash-freedom
  (define AxCfC
    (for/list ([Ki Ks])
      (match Ki
        [(list K 0) (term (cf [,K]))]
        [(list K n)
         (let ([xs (names 'x n)])
           (term (∀ ,xs ([cf [,K ,@ xs]] . ⇔ . [∧* ,@ (for/list ([x xs])
                                                        (term (cf ,x)))]))))])))
  
  (term (∧*
         (∀ (x) ([app bad x] = bad))
         (∀ (x) ([app unr x] = unr))
         (∀ (x) ([x . ≠ . unr] . ⇒ . ([app x bad] = bad)))
         (∀ (x) ([x . ≠ . bad] . ⇒ . ([app x unr] = unr)))
         (bad . ≠ . unr)
         ,@ AxDisjC ,@ AxDisjCBU ,@ AxInj ,@ AxCfC
         (cf unr) (¬ (cf bad)))))

;; returns all axioms generated for program
(define-metafunction halo′
  axioms : p -> φ
  [(axioms p) (,[Theory-T Ks] ∧ (P p))])

;; generate assertions from program and contract claim
(define-metafunction halo′
  gen : p (e ∈ c) -> {any ...}
  [(gen p [e ∈ c])
   (any_decs ... any_p ... any_¬e∈c ... [check-sat])
   (where {any_decs ...} ,(decs [term p]))
   (where {any_p ...} (z3 (axioms p)))
   (where {any_¬e∈c ...} (z3 (¬ (C e ∈ c))))])