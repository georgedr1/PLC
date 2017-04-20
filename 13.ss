;:  Single-file version of the interpreter.
;; Easier to submit to server probably harder to use in the development process

(load "chez-init.ss") 

;-------------------+
;                   |
;    DATATYPES      |
;                   |
;-------------------+

; parsed expression

(define-datatype expression expression?
  [var-exp
   (id symbol?)]
  [lambda-exp
   (id lambda-arg?)
   (body (list-of expression?))]
  [let-exp                          ;TODO Named
    (vars (list-of expression?))
    (body (list-of expression?))]
  [let*-exp
    (vars (list-of expression?))
    (body (list-of expression?))]
  [letrec-exp
    (vars (list-of expression?))
    (body (list-of expression?))]
  [app-exp
   (rator expression?)
   (rands (list-of expression?))]
  [if-exp
    (condition expression?)
    (body (list-of expression?))]
  [set!-exp
    (var expression?)
    (new expression?)]
  [lit-exp
    (id literal?)])

(define  lambda-arg?
  (lambda (v)
    (or (pair? v) (symbol? v) (null? v))))

(define  literal?
  (lambda (x)
    (ormap 
       (lambda (pred) (pred x))
       (list number? vector? boolean? symbol? string? pair? null?))))

	
	(define  unparse-exp
  (lambda (exp)
    (cases expression exp
      [var-exp (id) id]
      [lambda-exp (id body)
        (append (list 'lambda id)
          (map unparse-exp body))]
      [app-exp (rator rands)
        (append (list (unparse-exp rator))
              (map unparse-exp rands))]
      [if-exp (condition body)
        (append (list 'if 
            (unparse-exp condition)) 
            (map unparse-exp body))]
      [let-exp (vars body)
        (append (list 'let
                (map unparse-exp vars))
              (map unparse-exp body))]
      [let*-exp (vars body)
        (append (list 'let*
                (map unparse-exp vars))
              (map unparse-exp body))]
      [letrec-exp (vars body)
        (append (list 'letrec
                (map unparse-exp vars))
              (map unparse-exp body))]
      [set!-exp (var new)
        (list 'set! (unparse-exp var) (unparse-exp new))]
      [lit-exp (id) id])))

;; environment type definitions

(define  scheme-value?
  (lambda (x) #t))

(define-datatype environment environment?
  (empty-env-record)
  (extended-env-record
   (syms (list-of symbol?))
   (vals (list-of scheme-value?))
   (env environment?)))

; datatype for procedures.  At first there is only one
; kind of procedure but more kinds will be added later.

(define-datatype proc-val proc-val?
  [prim-proc
   (name symbol?)])
	 
	

;-------------------+
;                   |
;    PARSER         |
;                   |
;-------------------+


; This is a parser for simple Scheme expressions such as those in EOPL 3.1 thru 3.3.

; You will want to replace this with your parser that includes more expression types more options for these types and error-checking.

; Procedures to make the parser a little bit saner.
(define 1st car)
(define 2nd cadr)
(define 3rd caddr)

(define  parse-exp         
  (lambda (datum)
    (cond
     [(symbol? datum) (var-exp datum)]
     [(pair? datum)
      (cond
        [(eqv? (car datum) 'lambda)
          (cond [(and (null? (cddr datum)) (not (list? (2nd datum))))
              (eopl:error 'parse-exp "Error in parse-exp: lambda expression: lambda expression missing body")]
              [(null? (cddr datum))
              (eopl:error 'parse-exp "Error in parse-exp: lambda expression: incorrect length: ~s" datum)]
              [(and (list? (2nd datum)) (not ((list-of symbol?) (2nd datum))))
                (eopl:error 'parse-exp "Error in parse-exp: lambda argument list: formals must be symbols: ~s" (2nd datum))]
              [else
          (lambda-exp (2nd datum)
              (map parse-exp (cddr datum)))])]
      [(eqv? (car datum) 'if) 
        (cond   [(or (null? (cddr datum)) (and (not (null? (cdddr datum))) (not (null? (cddddr datum)))))
              (eopl:error 'parse-exp "Error in parse-exp: if expression: should have (only) test then and else clauses: ~s" datum)]
            [else     
              (if-exp (parse-exp (2nd datum))
                (map parse-exp (cddr datum)))])]
      [(eqv? (car datum) 'let)
        (cond [(or (null? (cdr datum)) (null? (cddr datum)))
            (eopl:error 'parse-exp "Error in parse-exp: let expression: incorrect length: ~s" datum)]
            [(not (list? (2nd datum)))
              (eopl:error 'parse-exp "Error in parse-exp: let decls: not a proper list: ~s" datum)]
            [else
            (let-exp (map parse-exp (2nd datum)) (map parse-exp (cddr datum)))])]
      [(eqv? (car datum) 'let*)
        (cond [(or (null? (cdr datum)) (null? (cddr datum)))
            (eopl:error 'parse-exp "Error in parse-exp: let* expression: incorrect length: ~s" datum)]
            [(not (list? (2nd datum)))
              (eopl:error 'parse-exp "Error in parse-exp: let* decls: not a proper list: ~s" datum)]
            [else
            (let*-exp (map parse-exp (2nd datum)) (map parse-exp (cddr datum)))])]
      [(eqv? (car datum) 'letrec)
        (cond [(or (null? (cdr datum)) (null? (cddr datum)))
            (eopl:error 'parse-exp "Error in parse-exp: letrec expression: incorrect length: ~s" datum)]
            [(not (list? (2nd datum)))
              (eopl:error 'parse-exp "Error in parse-exp: letrec decls: not a proper list: ~s" datum)]
            [else
            (letrec-exp (map parse-exp (2nd datum)) (map parse-exp (cddr datum)))])]
      [(eqv? (car datum) 'set!)
        (cond [(null? (cddr datum))
            (eopl:error 'parse-exp "Error in parse-exp: set!: missing  expression: ~s" datum)]
            [(not (null? (cdddr datum)))
              (eopl:error 'parse-exp "Error in parse-exp: set!: Too many parts: ~s" datum)]
            [else
            (set!-exp (parse-exp (2nd datum)) (parse-exp (3rd datum)))])] 
      [(eqv? (car datum) 'quote)
        (lit-exp (cadr datum))]
      [else 
          (cond [(not (list? datum))
              (eopl:error 'parse-exp "Error in parse-exp: pplication ~s is not a proper list" datum)]
              [else 
              (app-exp (parse-exp (1st datum))
              (map parse-exp (cdr datum)))])])]
     [(literal? datum) (lit-exp datum)]
     [else (eopl:error 'parse-exp "bad expression: ~s" datum)])))








;-------------------+
;                   |
;   ENVIRONMENTS    |
;                   |
;-------------------+





; Environment definitions for CSSE 304 Scheme interpreter.  
; Based on EoPL sections 2.2 and 2.3

(define  empty-env
  (lambda ()
    (empty-env-record)))

(define  extend-env
  (lambda (syms vals env)
    (extended-env-record syms vals env)))

(define  list-find-position
  (lambda (sym los)
    (list-index (lambda (xsym) (eqv? sym xsym)) los)))

(define  list-index
  (lambda (pred ls)
    (cond
     ((null? ls) #f)
     ((pred (car ls)) 0)
     (else (let ((list-index-r (list-index pred (cdr ls))))
	     (if (number? list-index-r)
		 (+ 1 list-index-r)
		 #f))))))

(define  apply-env
  (lambda (env sym succeed fail) ; succeed and fail are "callback procedures 
    (cases environment env       ;  succeed is appluied if sym is found otherwise 
      [empty-env-record ()       ;  fail is applied.
        (fail)]
      [extended-env-record (syms vals env)
		(let ((pos (list-find-position sym syms)))
      	  (if 	(number? pos)
				(succeed (list-ref vals pos))
				(apply-env env sym succeed fail)))])))








;-----------------------+
;                       |
;   SYNTAX EXPANSION    |
;                       |
;-----------------------+



; To be added later









;-------------------+
;                   |
;   INTERPRETER    |
;                   |
;-------------------+



; top-level-eval evaluates a form in the global environment

(define  top-level-eval
  (lambda (form)
    ; later we may add things that are not expressions.
    (eval-exp form)))

; eval-exp is the main component of the interpreter

(define  eval-exp
  (lambda (exp)
    (cases expression exp
      [lit-exp (datum) datum]
      [var-exp (id)
				(apply-env init-env id; look up its value.
      	   (lambda (x) x) ; procedure to call if it is in the environment 
           (lambda () (eopl:error 'apply-env ; procedure to call if it is not in env
		          "variable not found in environment: ~s"
			   id)))] 
      [app-exp (rator rands)
        (let ([proc-value (eval-exp rator)]
              [args (eval-rands rands)])
          (apply-proc proc-value args))]
      [if-exp (condition body)
        (if (eval-exp condition)
              (eval-exp (car body))
              (if (not (null? (cdr body)))
                    (eval-exp (cadr body))))]
      [lambda-exp (id body)
        (lambda (eval-exp id) (eval-exp body))]
      [else (eopl:error 'eval-exp "Bad abstract syntax: ~a" exp)])))

; evaluate the list of operands putting results into a list

(define  eval-rands
  (lambda (rands)
    (map eval-exp rands)))

;  Apply a procedure to its arguments.
;  At this point we only have primitive procedures.  
;  User-defined procedures will be added later.

(define  apply-proc
  (lambda (proc-value args)
    (cases proc-val proc-value
      [prim-proc (op) (apply-prim-proc op args)]
			; You will add other cases
      [else (eopl:error 'apply-proc
                   "Attempt to apply bad procedure: ~s" 
                    proc-value)])))

(define *prim-proc-names* '(+ - * / add1 sub1 cons = > < >= <= not and or car cdr list null? assq eq? equal? atom? zero? length list->vector 
  list? pair? procedure? vector->list vector make-vector vector-ref
  vector? number? symbol? set-car! set-cdr! vector-set! display newline caar cadr cddr cdar caaar caadr cadar caddr cdaar cdadr cddar cdddr))

(define init-env         ; for now our initial global environment only contains 
  (extend-env            ; procedure names.  Recall that an environment associates
     *prim-proc-names*   ;  a value (not an expression) with an identifier.
     (map prim-proc      
          *prim-proc-names*)
     (empty-env)))

; Usually an interpreter must define  each 
; built-in procedure individually.  We are "cheating" a little bit.

(define apply-prim-proc
  (lambda (prim-proc args)
    (case prim-proc
      [(+) (apply + args)]
      [(-) (apply - args)]
      [(*) (apply * args)]
      [(/) (apply / args)]
      [(add1) (+ (1st args) 1)]
      [(sub1) (- (1st args) 1)]
      [(cons) (cons (1st args) (2nd args))]
      [(=) (= (1st args) (2nd args))]
      [(>=) (>= (1st args) (2nd args))]
      [(>) (> (1st args) (2nd args))]
      [(<) (< (1st args) (2nd args))]
      [(<=) (<= (1st args) (2nd args))]
      [(not) (not (1st args))]
      [(and) (andmap (lambda (x) x) args)]
      [(or) (ormap (lambda (x) x) args)]
      [(car) (car (1st args))]
      [(cdr) (cdr (1st args))]
      [(list) args]
      [(null?) (null? (1st args))]
      [(assq) (assq (1st args) (2nd args))]
      [(eq?) (eq? (1st args) (2nd args))]
      [(equal?) (equal? (1st args) (2nd args))]
      [(atom?) (atom? (1st args))]
      [(zero?) (zero? (1st args))]
      [(length) (length (1st args))]
      [(list->vector) (list->vector (1st args))]
      [(list?) (list? (1st args))]
      [(pair?) (pair? (1st args))]
      [(procedure?) (procedure? (1st args))]
      [(vector->list) (vector->list (1st args))]
      [(vector) (apply vector args)]
      [(make-vector) 
        (if (eq? 2 (length args))
          (make-vector (1st args) (2nd args))
          (make-vector (1st args)))] 
      [(vector-ref) (vector-ref (1st args) (2nd args))]
      [(vector?) (vector? (1st args))]
      [(number?) (number? (1st args))]
      [(symbol?) (symbol? (1st args))]
      [(set-car!) (set-car! (1st args) (2nd args))]
      [(set-cdr!) (set-cdr! (1st args) (2nd args))]
      [(vector-set!) (vector-set! (1st args) (2nd args) (3rd args))]
      [(display) 
        (if (eq? 2 (length args))
          (display (1st args) (2nd args))
          (display (1st args)))] 
      [(caar) (caar (1st args))]
      [(cadr) (cadr (1st args))]
      [(cddr) (cddr (1st args))]
      [(cdar) (cdar (1st args))]
      [(caaar) (caaar (1st args))]
      [(caadr) (caadr (1st args))]
      [(cadar) (cadar (1st args))]
      [(caddr) (caddr (1st args))]
      [(cdddr) (cdddr (1st args))]
      [(cddar) (cddar (1st args))]
      [(cdadr) (cdadr (1st args))]
      [(cdaar) (cdaar (1st args))]
      [(newline) 
        (if (null? args)
          (newline)
          (newline (1st args)))] 
      [else (error 'apply-prim-proc 
            "Bad primitive procedure name: ~s" 
            prim-proc)])))

(define  rep      ; "read-eval-print" loop.
  (lambda ()
    (display "--> ")
    ;; notice that we don't save changes to the environment...
    (let ([answer (top-level-eval (parse-exp (read)))])
      ;; TODO: are there answers that should display differently?
      (eopl:pretty-print answer) (newline)
      (rep))))  ; tail-recursive so stack doesn't grow.

(define  eval-one-exp
  (lambda (x) (top-level-eval (parse-exp x))))









