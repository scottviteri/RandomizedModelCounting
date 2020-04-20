(load "propositional-logic.scm")

;;;;;;;; combinators and common functions ;;;;;;;;;

(define id (lambda (x) x))
(define (pa f x) (lambda (y) (f x y)))
(define (pa-2 f x y) (lambda (z) (f x y z)))
(define (flip f) (lambda (x y) (f y x)))
(define (run f) (f))
(define const (lambda (x) (lambda (y) x)))
(define (compose-2 f g h) (lambda (x) (f (g x) (h x))))

(define (tree-size t)
  ;(tree-size '(∧ (∨ 2 4) 3)) ;5
  (if (leaf? t) 1 (+ 1 (tree-size (cadr t)) (tree-size (caddr t)))))
(define average (compose-2 / (pa apply +) length))

(define (display-list lst) (map (lambda (x) (begin (display x) (newline))) lst))
(define (enumerate-and-display-list lst)
  (display-list (zip (iota (length lst)) lst)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;; Guess whether a formula is valid by random sampling of models ;;;;;;;;;;;
;;;;;;;;;  Inaccurate but computationally efficient                     ;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (generate-formula prob-expansion decay num-vars)
  ;(generate-formula .9 .8 3) ;(∨ -2 (∨ 3 -3)) <-- random
  (define (generate-random-tree prob-of-expansion decay)
    (define (sample-list lst)
      (list-ref lst (random (length lst))))
    (define (generate-random-tree-aux prob-of-expansion)
      (if (> (random:uniform) prob-of-expansion)
          'x
          (let ((bin-op (sample-list '(∧ ∨ ⇒))))
            (list bin-op
                  (generate-random-tree-aux (* decay prob-of-expansion))
                  (generate-random-tree-aux (* decay prob-of-expansion))))))
    (generate-random-tree-aux prob-of-expansion))
  (define (generate-formula-aux formula-tree)
    (if (leaf? formula-tree)
        (* (expt -1 (random 2)) (+ 1 (random num-vars)))
        (list (car formula-tree)
              (generate-formula-aux (cadr formula-tree))
              (generate-formula-aux (caddr formula-tree)))))
  (let ((formula-tree (generate-random-tree prob-expansion decay)))
    (generate-formula-aux formula-tree)))


(define (generate-random-models formula num-models)
  (define (sample-true-false) (if (> (random 2) 0) #t #f))
  (define (generate-random-model formula)
    ;((generate-random-model '(∨ -2 (∨ 3 -3)))) ;((3 . #f) (2 . #t))
    (lambda ()
      (let* ((unique-vars (get-unique-vars formula))
             (random-model (map (compose run (const sample-true-false))
                                (iota (length unique-vars)))))
        (map cons unique-vars random-model))))
  (map (compose run (const (generate-random-model formula))) (iota num-models)))

(define fraction-true
  ;(fraction-true '(#t #f #f)) ;0.3333333333333333
  (let ((exact-if-integer
         (lambda (frac) (let* ((boolean-or (lambda (p q) (if p #t q)))
                          (0-or-1? (compose-2 boolean-or (pa equal? 0) (pa equal? 1))))
                      (if (0-or-1? frac) frac (exact->inexact frac)))))
        (keep-if-true (pa filter id)))
    (compose exact-if-integer (compose-2 / (compose length keep-if-true) length))))


(define (guess-valid-fraction formula num-models)
  (let ((random-models (generate-random-models formula num-models)))
    (fraction-true (map (lambda (model) (evaluate formula model)) random-models))))

(define (guess-valid formula num-models)
  (equal? 1 (guess-valid-fraction formula num-models)))

(define (guess-valid-false-positive-rate prob-expansion decay num-vars num-models)
  ;(guess-valid-false-positive-rate .9 .881 6 256)
  ;Average formula size: 42.0
  ;Average num operations: 20.5
  ;0.2 (or 0.1)
  (let ((formulas (map (lambda (_) (generate-formula prob-expansion decay num-vars)) (iota 10))))
    ;(enumerate-and-display-list formulas) (newline)
    (display "Average formula size: ") (display (exact->inexact (average (map tree-size formulas)))) (newline)
    (display "Average num operations: ") (display (exact->inexact (average (map count-operations formulas)))) (newline)
    (fraction-true (map (pa (flip guess-valid) num-models)
                        formulas))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;; Check true model fraction -- exact but computationally inefficient ;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define make-unique
  ;(make-unique '(1 2 3 2 1)) ;(3 2 1)
  (pa-2
   fold
   (lambda (next acc)
     (if (member next acc) acc (cons next acc)))
   '()))


(define (check-true-model-fraction formula)
  ;(check-true-model-fraction (list '∧ 1 2)) ;0.25
  ;(check-true-model-fraction (list '∨ 1 2)) ;0.75
  (define (generate-all-models formula)
    ;(generate-all-models (list '∧ 1 2))
    ;(((2 . 0) (1 . 0)) ((2 . 0) (1 . 1)) ((2 . 1) (1 . 0)) ((2 . 1) (1 . 1)))
    (define (repeat n k) (map (const n) (iota k))) ; (repeat 10 3) ; (10 10 10)
    (define (convert-to-binary num)
      (reverse (unfold (pa >= 0)
                       (pa (flip truncate-remainder) 2)
                       (pa (flip truncate-quotient) 2)
                       num)))
    (define (convert-to-binary-fixed-digits num num-digits)
      (let* ((bin-rep (convert-to-binary num))
             (padding (repeat 0 (- num-digits (length bin-rep)))))
        (append padding bin-rep)))
    (define (integer->bool x) (if (= 0 x) #f #t))
    (let* ((unique-vars (get-unique-vars formula))
           (num-unique-vars (length unique-vars))
           (num-models (expt 2 num-unique-vars))
           (generate-model-values (lambda (i) (map integer->bool
                                              (convert-to-binary-fixed-digits i num-unique-vars)))))
      (map (lambda (i) (map cons unique-vars (generate-model-values i)))
           (iota num-models))))

  (let* ((all-models (generate-all-models formula)))
    (fraction-true (map (pa evaluate formula) all-models))))

(define (average-fraction-true-models-given-valid prob-expansion decay num-vars)
  ;(average-fraction-true-models-given-valid .9 .881 6)
  ;Average formula size: 38.54
  ;Average num operations: 18.77
  ;Fraction valid: 0.2
  ;0.61640625
  (let* ((formulas (map (lambda (_) (generate-formula prob-expansion decay num-vars)) (iota 100)))
         (invalid-formula-fractions (filter (compose not (pa = 1)) (map check-true-model-fraction formulas))))
    ;(enumerate-and-display-list formulas) (newline)
    (display "Average formula size: ") (display (exact->inexact (average (map tree-size formulas)))) (newline)
    (display "Average num operations: ") (display (exact->inexact (average (map count-operations formulas)))) (newline)
    (display "Fraction valid: ") (display (exact->inexact (- 1 (/ (length invalid-formula-fractions) (length formulas))))) (newline)
    (average invalid-formula-fractions)))



;;;;;;;  Formula Entailment ;;;;;;;;

(define (check-entailment-fraction f1 f2)
  (check-true-model-fraction (list '⇒ f1 f2)))

(define (guess-entailment-fraction f1 f2 num-models)
  (guess-valid-fraction (list '⇒ f1 f2) num-models))

(define (guess-entailment f1 f2 num-models)
  (guess-valid (list '⇒ f1 f2) num-models))

(guess-entailment 1 1 10) ;#t
(guess-entailment (list '∧ 1 2) 1 10) ;#t
(guess-entailment (list '∨ 1 2) 1 10) ;#f <- probably
(check-entailment-fraction (list '∨ 1 2) 1) ; 3/4
(guess-entailment-fraction (list '∨ 1 2) 1 1000) ; ~3/4

(define a '(∧ (⇒ (⇒ -4 3) 3) (∨ -4 (∧ -5 -5))))
(define b '(∧ -4 (⇒ 4 (∧ (∨ -4 3) -4))))
(guess-entailment a b 1000) ; #f <-- probably

(define* (generate-random-entailment-pairs prob-expansion decay num-vars #:optional (debug #f))
  (define (flatten lst) (fold append '() lst))
  (define (product l1 l2) (flatten (map (lambda (x) (map (lambda (y) (cons x y)) l2)) l1)))
  (define (self-product l1) (make-unique (product l1 l1)))
  (define (remove-identity pairs) (filter (lambda (x) (not (equal? (car x) (cdr x)))) pairs))
  (let* ((random-formulas (make-unique (map (lambda (_) (generate-formula prob-expansion decay num-vars)) (iota 10))))
         (formula-pairs (remove-identity (self-product (iota (length random-formulas))))))
    (if debug (begin
                (display "Formulas:") (newline)
                (display-list (zip (iota (length random-formulas)) random-formulas)) (newline)
                (display "Entailment Pairs:") (newline)))
    (receive (entailments non-entailments)
        (partition (lambda (x) (check-entailment (list-ref random-formulas (car x))
                                            (list-ref random-formulas (cdr x)))) formula-pairs)
      (list random-formulas entailments non-entailments))))

(define (generate-entailment-dataset prob-expansion decay num-vars)
  ;creates a dataset of 50/50 entailment/non-entailment pairs
  ;(generate-entailment-dataset .9 .8 5)
  (match-let (((formulas ent non-ent)
               (generate-random-entailment-pairs prob-expansion decay num-vars)))
    (let ((smaller-length (min (length ent) (length non-ent))))
      (list formulas (take ent smaller-length) (take non-ent smaller-length)))))


(define (guess-entailment-false-positive-rate prob-expansion decay num-vars num-guesses)
  ;(guess-entailment-false-positive-rate .9 .881 6 256)
  ;Average formula size: 48.333333333333336
  ;Average num operations: 23.666666666666668
  ;$16 = 0
  (match-let* (((formulas ent non-ent)
                (generate-entailment-dataset prob-expansion decay num-vars)))
    ;(enumerate-and-display-list formulas) (newline) (display ent) (newline)
    (display "Average formula size: ") (display (exact->inexact (average (map tree-size formulas)))) (newline)
    (display "Average num operations: ") (display (exact->inexact (average (map count-operations formulas)))) (newline)
    (fraction-true (map (lambda (p) (guess-entailment (list-ref formulas (car p))
                                                 (list-ref formulas (cdr p))
                                                 num-guesses))
                        non-ent))))

(define (generate-random-entailment-quadruples prob-expansion decay num-vars desired-num-quadruples max-tries)
  ; this bit is too slow, could make faster by implementing Tseitin transform
  (define (sample-k-from-list k lst)
    (define (remove-index lst i)
      (append (list-head lst i) (list-tail lst (+ i 1))))
    (define (sample-k-from-list-aux k lst removed-elems)
      (if (= k 0) removed-elems
          (let ((removal-index (random (length lst))))
            (sample-k-from-list-aux
             (- k 1)
             (remove-index lst removal-index)
             (cons (list-ref lst removal-index) removed-elems)))))
    (sample-k-from-list-aux k lst '()))

  (define (all lst) (fold (lambda (next acc) (if acc next #f)) #t lst))

  (let* ((random-formulas (make-unique (map (lambda (_) (generate-formula prob-expansion decay num-vars)) (iota 10)))))
    (define (generate-random-entailment-quadruples-aux quadruples max-tries)
      (if (or (= 0 max-tries) (>= (length quadruples) desired-num-quadruples))
          quadruples
          (let ((quadruple-indices (sample-k-from-list 4 (iota (length random-formulas)))))
            (match-let (((a1 b1 a2 b2) (map (lambda (i) (list-ref random-formulas i)) quadruple-indices)))
              (if (all (map check-valid `((⇒ ,a1 ,b1) (¬ (⇒ ,a1 ,b2)) (¬ (⇒ ,a2 ,b1)) (⇒ ,a2 ,b2))))
                  (generate-random-entailment-quadruples-aux (cons quadruple-indices quadruples) (- max-tries 1))
                  (generate-random-entailment-quadruples-aux quadruples (- max-tries 1)))))))
    (generate-random-entailment-quadruples-aux '() max-tries)))
