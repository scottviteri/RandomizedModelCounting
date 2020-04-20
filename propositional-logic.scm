(use-modules
 (srfi srfi-1)
 (ice-9 match)
 (ice-9 popen)
 (ice-9 rdelim)
 (ice-9 receive))

;;;;;;; Convert propositional formula to CNF form ;;;;;;;;;;;

(define leaf? (compose not list?))

(define (get-vars t)
  (match t
    ((? leaf? x) (list x))
    ((op x) (get-vars x))
    ((op x y) (append (get-vars x) (get-vars y)))
    ((op x ...) (fold append '() (map get-vars x)))))

(define (count-operations t)
  ;(count-operations '(∧ (⇒ (⇒ -4 3) 3) (∨ -4 (∧ -5 -5)))) ;5
  ;(count-operations '(∧ (∨ -2 -1 -1 3 1 -1) (∨ -2 -1 -1 -1 -1) (∨ -2 -1 -1 1 -1) (∨ -2 2 -1 3 1 -1) (∨ -2 2 -1 -1 -1) (∨ -2 2 -1 1 -1))) ;7
  (match t
    ((? leaf? x) 0)
    ((op x) (+ 1 (count-operations x)))
    ((op x y) (+ 1 (count-operations x) (count-operations y)))
    ((op x ...) (+ 1 (apply + (map count-operations x))))))

(define (make-vars-unique lst)
  (fold (lambda (next acc) (if (member (abs next) acc)
                          acc
                          (cons (abs next) acc)))
        '() lst))

(define count-vars
  ;(count-vars '(∧ (∨ 2 4) 3)) ;3
  (compose length get-vars))

(define get-unique-vars (compose make-vars-unique get-vars))
(define count-unique-vars (compose length get-unique-vars))

(define test-formula '(∨ -2 (⇒ (∧ 1 (⇒ -1 -2)) (⇒ 1 (∧ (∧ -1 (⇒ -3 1)) 1)))))

(define (remove-implication formula)
  (match formula
    ((? leaf? s) s)
    ((op s)      (list op (remove-implication s)))
    (('⇒ s t)    (list '∨ (remove-implication (list '¬ s)) (remove-implication t)))
    ((op s t)    (list op (remove-implication s) (remove-implication t)))))

(remove-implication test-formula) ;(∨ -2 (∨ (¬ (∧ 1 (∨ (¬ -1) -2))) (∨ (¬ 1) (∧ (∧ -1 (∨ (¬ -3) 1)) 1))))

(define (remove-negation formula)
  (match formula
    ((? leaf? s) s)
    (('¬ (? leaf? s)) (* -1 s))
    (('¬ ('¬ s)) (remove-negation s))
    (('¬ ('∧ s t)) (list '∨ (remove-negation (list '¬ s)) (remove-negation (list '¬ t))))
    (('¬ ('∨ s t)) (list '∧ (remove-negation (list '¬ s)) (remove-negation (list '¬ t))))
    ((bin-op s t) (list bin-op (remove-negation s) (remove-negation t)))))

(remove-negation '(¬ -1)) ; 1
(remove-negation '(¬ (∨ -1 2))) ;(∧ 1 -2)
(remove-negation '(¬ (¬ -1))) ; -1
(remove-negation (remove-implication test-formula))
; (∨ -2 (∨ (∨ -1 (∧ -1 2)) (∨ -1 (∧ (∧ -1 (∨ 3 1)) 1))))

(define (fixpoint f x)
  (define (fixpoint-aux prev)
    (let ((next (f prev))) (if (equal? prev next) prev (fixpoint-aux next))))
  (fixpoint-aux x))

(define (push-or-below-and formula)
  (define (push-or-below-and-aux formula)
    (match formula
      ((? leaf? s)       s)
      (('∨ ('∧ j k) l) (push-or-below-and-aux (list '∧ (list '∨ j l) (list '∨ k l))))
      (('∨ j ('∧ k l)) (push-or-below-and-aux (list '∧ (list '∨ j k) (list '∨ j l))))
      ((op s t)          (list op (push-or-below-and-aux s) (push-or-below-and-aux t)))))
  (fixpoint push-or-below-and-aux formula))

(push-or-below-and (remove-negation (remove-implication test-formula)))
;(∧ (∧ (∧ (∨ -2 (∨ (∨ -1 -1) (∨ -1 -1))) (∨ -2 (∨ (∨ -1 -1) (∨ -1 (∨ 3 1))))) (∨ -2 (∨ (∨ -1 -1) (∨ -1 1)))) (∧ (∧ (∨ -2 (∨ (∨ -1 2) (∨ -1 -1))) (∨ -2 (∨ (∨ -1 2) (∨ -1 (∨ 3 1))))) (∨ -2 (∨ (∨ -1 2) (∨ -1 1)))))

(define (collect flatten? formula)
  (if (leaf? formula) formula
      (reverse (fold (lambda (a b) (if (or (leaf? a) (not (flatten? a)))
                                  (cons a b)
                                  (append (collect flatten? (reverse (cdr a))) b)))
                     '() formula))))

(define (collect-conjs formula)
  (collect (lambda (x) (equal? '∧ (car x))) formula))

(define (collect-disjs formula)
  (cond ((leaf? formula) formula)
        ((equal? '∨ (car formula)) (collect (lambda (y) (equal? '∨ (car y))) formula))
        (else
         (map (lambda (x) (if (or (leaf? x) (not (equal? '∨ (car x))))
                         x
                         (collect (lambda (y) (equal? '∨ (car y))) x)))
              formula))))

(define collect-conjs-and-disjs (compose collect-disjs collect-conjs))

(define formula->cnf (compose collect-conjs-and-disjs push-or-below-and remove-negation remove-implication))

(formula->cnf test-formula)
;(∧ (∨ -2 -1 -1 3 1 -1) (∨ -2 -1 -1 -1 -1) (∨ -2 -1 -1 1 -1) (∨ -2 2 -1 3 1 -1) (∨ -2 2 -1 -1 -1) (∨ -2 2 -1 1 -1))


(define (write-to-dimacs cnf)
  (let* ((tempfile (open-output-file "temp.dimacs"))
         (num-vars (count-unique-vars cnf))
         (stripped-cnf (map (lambda (x) (if (leaf? x) x (cdr x))) (cdr cnf)))
         (num-clauses (length stripped-cnf)))
    (write 'p tempfile) (write-char #\space tempfile) (write 'cnf tempfile) (write-char #\space tempfile)
    (write num-vars tempfile) (write-char #\space tempfile) (write num-clauses tempfile) (write-char #\newline tempfile)
    (map (lambda (line)
           (begin
             (if (leaf? line)
                 (begin (write line tempfile) (write-char #\space tempfile))
                 (map (lambda (num) (begin (write num tempfile)
                                      (write-char #\space tempfile))) line))
             (write 0 tempfile)
             (write-char #\newline tempfile)))
         stripped-cnf)
    (write-char #\newline tempfile)
    (close-output-port tempfile)))

(define (check-sat formula)
  (write-to-dimacs (formula->cnf formula))
  (let* ((port (open-input-pipe "z3 -dimacs temp.dimacs"))
         (str (read-line port)))
    (close-pipe port)
    (if (equal? str "sat") #t #f)))

(define (check-valid formula)
  (not (check-sat (list '¬ formula))))

(define (check-entailment f1 f2)
  (check-valid (list '⇒ f1 f2)))

(check-entailment 1 1) ;#t
(check-entailment (list '∧ 1 2) 1) ;#t
(check-entailment (list '∨ 1 2) 1) ;#f

;;;;;;  evaluate propositional formula given a model  ;;;;;;;;;;;

(define (evaluate formula model)
  (define (evaluate-aux formula)
    (if (leaf? formula)
            (if (or (not (integer? formula)) (> formula 0))
            (assoc-ref model formula)
            (not (assoc-ref model (* -1 formula)))) ; negative integer means negative variable position
        (let ((operation (car formula)))
          (match operation
            ('¬ (not (evaluate-aux (cadr formula))))
            ('∧ (and (evaluate-aux (cadr formula))
                     (evaluate-aux (caddr formula))))
            ('∨ (or (evaluate-aux (cadr formula))
                     (evaluate-aux (caddr formula))))
            ('⇒ (or (not (evaluate-aux (cadr formula)))
                    (evaluate-aux (caddr formula))))
            ('⊕ (let ((left (evaluate-aux (cadr formula))) (right (evaluate-aux (caddr formula))))
                  (or (and left (not right)) (and (not left) right))))
            ('⇔ (let ((left (evaluate-aux (cadr formula))) (right (evaluate-aux (caddr formula))))
                  (or (and left right) (and (not left) (not right)))))))))
  (evaluate-aux formula))

(evaluate 'x '((x . #t))) ;#t
(evaluate '(∧ x y) '((x . #t) (y . #t))) ;#t
(evaluate '(∧ x y) '((x . #t) (y . #f))) ;#f
(evaluate '(∧ (⇒ (⇒ -4 3) 3) (∨ -4 (∧ -5 -5))) '((3 . #t) (4 . #t) (5 . #f))) ; #t
(evaluate '(∧ -4 (⇒ 4 (∧ (∨ -4 3) -4))) '((3 . #t) (4 . #t) (5 . #f))) ; #f
