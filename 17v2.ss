;:  Single-file version of the interpreter.
;; Easier to submit to server probably harder to use in the development process

 (load "C:/Users/kildufje/Documents/School/Senior/Spring/CSSE304/PLC/chez-init.ss")
;(load "C:/Users/georgedr/Documents/Class stuff/Spring 16-17/PLC/PLC/chez-init.ss")

;TODO: Ask about why subst-leftmost on letrec isn't working
;TODO: Ask about why while only loops one time
;TODO: Ask about changing env with set!

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
  [let-exp                          
    (vars (list-of let-var?))
    (body (list-of expression?))]
  [named-let-exp
    (proc-id symbol?)
    (vars (list-of let-var?))
    (body (list-of expression?))]
  [let*-exp
    (vars (list-of expression?))
    (body (list-of expression?))]
  [letrec-exp
    (vars (list-of expression?))
    (body (list-of expression?))]
  [begin-exp
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
  [cond-exp
    (conditiions (list-of expression?))
    (bodies (list-of expression?))]
  [lit-exp
    (id literal?)]
  [case-exp
    (expr0 expression?)
    (keys (list-of expression?))
    (exprs (list-of (list-of expression?)))]
  [while-exp
    (test expression?)
    (bodies (list-of expression?))])

(define let-var?
  (lambda (x)
    (and (list? x) (eq? (length x) 2) (symbol? (car x)) (expression? (cadr x)))))

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
      [lit-exp (id) id]
      [else (eopl:error 'unparse-exp:  ; procedure to call if it is not in env
              "unparse nopt defined for : ~s"
         exp)])))

;; environment type definitions

(define  scheme-value?
  (lambda (x) #t))

(define-datatype environment environment?
  (empty-env-record)
  (extended-env-record
   (syms (list-of symbol?))
   (vals (list-of scheme-value?))
   (env environment?))
  [recursively-extended-env-record
(proc-names (list-of symbol?))
(idss (list-of pair?))
(bodiess (list-of (list-of expression?)))
(env environment?)])

; datatype for procedures.  At first there is only one
; kind of procedure but more kinds will be added later.

(define-datatype proc-val proc-val?
  [prim-proc
   (name symbol?)]
  [proc
    (name procedure?)]
  [closure
    (ids lambda-arg?)
    (bodies (list-of expression?))
    (env environment?)])
	 
; An auxiliary procedure that could be helpful.
(define var-exp?
 (lambda (x)
   (cases expression x
     [var-exp (id) #t]
     [else #f])))

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
            [(symbol? (2nd datum))
            (named-let-exp
              (2nd datum)
              (map list (map car (3rd datum))             ;vars
                          (map (lambda (x) (parse-exp (cadr x))) (3rd datum))) 
                (map parse-exp (cdddr datum)))]
            [(not (list? (2nd datum)))
              (eopl:error 'parse-exp "Error in parse-exp: let decls: not a proper list: ~s" datum)]
			[(not ((list-of symbol?) (map car (2nd datum))))
				(eopl:error 'parse-exp "first members must be symbols for let args: ~s" (2nd datum))]
			[(and (not (null? (2nd datum))) (not (andmap (lambda (x) (eq? 2 (length x))) (2nd datum))))
				(eopl:error 'parse-exp "let args must all be 2-lists: ~s" (2nd datum))]
            [else
            (let-exp 
                (map list (map car (2nd datum))             ;vars
                          (map (lambda (x) (parse-exp (cadr x))) (2nd datum))) 
                (map parse-exp (cddr datum)))])] ;body
      [(eqv? (car datum) 'let*)
        (cond [(or (null? (cdr datum)) (null? (cddr datum)))
            (eopl:error 'parse-exp "Error in parse-exp: let* expression: incorrect length: ~s" datum)]
            [(not (list? (2nd datum)))
              (eopl:error 'parse-exp "Error in parse-exp: let* decls: not a proper list: ~s" datum)]
			[(not ((list-of symbol?) (map car (2nd datum))))
				(eopl:error 'parse-exp "first members must be symbols for let* args: ~s" (2nd datum))]
            [(and (not (null? (2nd datum))) (not (andmap (lambda (x) (eq? 2 (length x))) (2nd datum))))
				(eopl:error 'parse-exp "let* args must all be 2-lists: ~s" (2nd datum))]
			[else
            (let*-exp (map parse-exp (2nd datum)) (map parse-exp (cddr datum)))])]
      [(eqv? (car datum) 'letrec)
        (cond [(or (null? (cdr datum)) (null? (cddr datum)))
            (eopl:error 'parse-exp "Error in parse-exp: letrec expression: incorrect length: ~s" datum)]
            [(not (list? (2nd datum)))
              (eopl:error 'parse-exp "Error in parse-exp: letrec decls: not a proper list: ~s" datum)]
			[(not ((list-of symbol?) (map car (2nd datum))))
				(eopl:error 'parse-exp "first members must be symbols for letrec args: ~s" (2nd datum))]
            [(and (not (null? (2nd datum))) (not (andmap (lambda (x) (eq? 2 (length x))) (2nd datum))))
				(eopl:error 'parse-exp "letrec args must all be 2-lists: ~s" (2nd datum))]
			[else
            (letrec-exp (map parse-exp (2nd datum)) (map parse-exp (cddr datum)))])]
      [(eqv? (car datum) 'set!)
        (cond [(null? (cddr datum))
            (eopl:error 'parse-exp "Error in parse-exp: set!: missing  expression: ~s" datum)]
            [(not (null? (cdddr datum)))
              (eopl:error 'parse-exp "Error in parse-exp: set!: Too many parts: ~s" datum)]
            [else
            (set!-exp (parse-exp (2nd datum)) (parse-exp (3rd datum)))])]
      [(eqv? (car datum) 'begin)
            (begin-exp (map parse-exp (cdr datum)))]
      [(eqv? (car datum) 'cond)
        (cond-exp 
            (map parse-exp (map car (cdr datum)))
            (map parse-exp (map cadr (cdr datum))))]
      [(eqv? (car datum) 'case)
        (case-exp 
            (parse-exp (cadr datum))
            (map parse-exp (map car (cddr datum)))
            (map parse-exp (map cadr (cddr datum))))]
      [(eqv? (car datum) 'quote)
        (lit-exp (cadr datum))]
      [(eqv? (car datum) 'while)
        (while-exp 
          (parse-exp (cadr datum))
          (map parse-exp (cddr datum)))]
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

(define extend-env-recursively
(lambda (proc-names idss bodiess old-env)
  ; (display "extend-env-recursively\n")
  ; (display "idss ")
  ;   (display idss)
  ;   (display "\n")
  ;   (display "bodies ")
  ;   (display bodiess)
  ;   (display "\n")
  ;   (display "proc names ")
  ;   (display proc-names)
  ;   (display "\n")
  ;   (display "old-env ")
  ;   (display old-env)
  ;   (display "\n")
(recursively-extended-env-record
proc-names idss bodiess old-env)))

(define  list-find-position
  (lambda (sym los)
    ; (display "list-find-position\n")
    (list-index (lambda (xsym) (eqv? sym xsym)) los)))

(define  list-index
  (lambda (pred ls)
    ; (display "list-index\n")
    (cond
     ((null? ls) #f)
     ((pred (car ls)) 0)
     (else (let ((list-index-r (list-index pred (cdr ls))))
	     (if (number? list-index-r)
		 (+ 1 list-index-r)
		 #f))))))

(define apply-env
  (lambda (env sym succeed fail) ; succeed and fail are "callback procedures 
    ; (display "apply-env\n")
    (cases environment env       ;  succeed is appluied if sym is found otherwise 
      [empty-env-record ()       ;  fail is applied.
        (fail)]
      [extended-env-record (syms vals env)
		(let ((pos (list-find-position sym syms)))
      	  (if 	(number? pos)
				(succeed (list-ref vals pos))
				(apply-env env sym succeed fail)))]
      [recursively-extended-env-record (procnames idss bodiess old-env)
        (let ([pos (list-find-position sym procnames)])
          (if (number? pos)
            (closure (list-ref idss pos)
                      (list-ref bodiess pos)
                      env)
            (apply-env old-env sym succeed fail)))])))








;-----------------------+
;                       |
;   SYNTAX EXPANSION    |
;                       |
;-----------------------+



(define syntax-expand
    (lambda (exp)
        ; (display "syntax-expand\n")
        (cases expression exp
          [var-exp (id) exp]
          [lit-exp (id) exp]
          [app-exp (rator rands) (app-exp rator (map syntax-expand rands))]
          [lambda-exp (id body) 
            (lambda-exp id (map syntax-expand body))]
          [let-exp (vars body)
            (app-exp 
              (lambda-exp (map car vars) (map syntax-expand body))
              (map syntax-expand (map cadr vars)))]
          [letrec-exp (ids bodies)
            ;(display ids)
            (letrec-exp
                (map syntax-expand ids)
                (map syntax-expand bodies))]
          [named-let-exp (proc-id vars body)
            ; (display vars)
            (letrec-exp
              (list (app-exp (var-exp proc-id) (list (lambda-exp (map car vars) (map syntax-expand body)))))
              (list (app-exp (var-exp proc-id) (map parse-exp (map cadadr vars)))))]
          [if-exp (condition body) 
            (if-exp (syntax-expand condition) (map syntax-expand body))]
          [set!-exp (var new)
            (set!-exp var (syntax-expand new))]
          [begin-exp (body)
            (syntax-expand (let-exp '() (map syntax-expand body)))]
          [cond-exp (conditions bodies)
            (cond [(and (null? (cdr conditions)) (eqv? (unparse-exp (car conditions)) 'else))
                    (syntax-expand (car bodies))]
                  [(null? (cdr conditions))
                    (if-exp (syntax-expand (car conditions)) (list (syntax-expand (car bodies))))]
                  [else
                    (if-exp (syntax-expand (car conditions)) (list (syntax-expand (car bodies)) (syntax-expand (cond-exp (cdr conditions) (cdr bodies)))))])]
          ;[case-exp (expr0 keys exprs)]
            ;(syntax-expand (cond-exp (ormap ))]
         [while-exp (test bodies)
           (syntax-expand (named-let-exp 'loop '((dummy (lit-exp 1))) (list (if-exp test (append bodies (list (app-exp (var-exp 'loop) (list (lit-exp '())))))))))]
          [else exp])))




;-------------------+
;                   |
;   INTERPRETER    |
;                   |
;-------------------+



; top-level-eval evaluates a form in the global environment

(define  top-level-eval
  (lambda (form)
    ; later we may add things that are not expressions.
    (eval-exp form init-env)))

; eval-exp is the main component of the interpreter

(define eval-exp
  (lambda (exp env)
    ; (display "eval-exp\n")
    ; (display env)
    ; (display "\n")
    (cases expression exp
      [lit-exp (datum) datum]
      [var-exp (id)
				(apply-env env id; look up its value.
      	   (lambda (x) x) ; procedure to call if it is in the environment 
           (lambda () (eopl:error 'apply-env ; procedure to call if it is not in env
		          "variable not found in environment: ~s"
			   id)))] 
      [app-exp (rator rands)
        (let ([proc-value (eval-exp rator env)]
              [args (eval-rands rands env)])
            (apply-proc proc-value args))]
      [if-exp (condition body)
        (if (eval-exp condition env)
              (eval-exp (car body) env)
              (if (not (null? (cdr body)))
                    (eval-exp (cadr body) env)))]
      [let-exp (vars body)
        (let ((extended-env (extend-env 
                                      (map car vars)
                                      (map (lambda (x) (eval-exp x env)) (map cadr vars))
                                      env)))
          (eval-let-bodies body extended-env))]
      [letrec-exp (ids bodies)
        (eval-let-bodies bodies
          (extend-env-recursively (map cadadr ids) (map cadr (map caaddr ids)) (map caddr (map caaddr ids)) env))]
      [lambda-exp (id body)
        (closure id body env)
        ; (cond [(list? id)
        ;         (proc
        ;           (lambda (vals)           
        ;             (let ((extended-env (extend-env 
        ;                                           id
        ;                                           vals
        ;                                           env)))
        ;            (eval-let-bodies body extended-env))))]
        ;       [(pair? id)
        ;         (let* ([prop-id (improper-2-proper id)]
        ;                [id-len (length prop-id)])
        ;         (proc
        ;           (lambda (vals)
        ;             (let ((extended-env (extend-env 
        ;                                           prop-id
        ;                                           (append (list-head vals (sub1 id-len)) (list (list-tail vals (sub1 id-len))))
        ;                                           env)))
        ;            (eval-let-bodies body extended-env)))))]
        ;       [(symbol? id) 
        ;         (proc
        ;           (lambda (vals)           
        ;             (let ((extended-env (extend-env 
        ;                                           (list id)
        ;                                           (list vals)
        ;                                           env)))
        ;            (eval-let-bodies body extended-env))))])
        ]
         [set!-exp (var new)
          ; eval new
          ; find var in env
          ; use list ref to change value to new 
          (let* ([new-val (eval-exp new env)]
                [new-env (set!-in-env var new-val env)])
                (set! env new-env)
            )]



      ; [while-exp (test bodies)
      ; (eval-while (test bodies ))
      ;   (if (eval-exp test env)
      ;         (begin
      ;           (newline)
      ;           (display 1)              
      ;           (map (lambda (x) (eval-exp x env)) bodies)
      ;           (eval-exp (while-exp test bodies) (extend-env 

      ;                                                         env))
      ;         #f))]
      [else (eopl:error 'eval-exp "Bad abstract syntax: ~a" exp)])))

(define set!-in-env 
  (lambda (var new-val env)
    (cases environment env       ;  succeed is appluied if sym is found otherwise 
      [empty-env-record ()       ;  fail is applied.
        (eopl:error 'set!-in-env "var not found: ~a" var)]
      [extended-env-record (syms vals next-env)
        (let ([pos (list-find-position (cadr var) syms)])
                ; (display vals)
                ; (display "\n")
                ; (display (list->vector vals))
                ; (display "\n")
                ; (display (vector-set! (list->vector vals) pos new-val))
                ; (display "\n")
                (if (number? pos)
                        (let ([vec (list->vector vals)])
                          (vector-set! vec pos new-val)
                          (extended-env-record syms (vector->list vec) next-env))
                        (extended-env-record syms vals (set!-in-env var new-val next-env))))]
      [else
        (eopl:error 'set!-in-env "wrong env: ~a" var)])))
      ; [recursively-extended-env-record (procnames idss bodiess old-env)
      ;   (let ([pos (list-find-position sym procnames)])
      ;     (if (number? pos)
      ;       (closure (list-ref idss pos)
      ;                 (list-ref bodiess pos)
      ;                 env)
      ;       (apply-env old-env sym succeed fail)))])))
   


(define eval-while
  (lambda (test bodies env)
    (if (eval-exp test env)
          (let ()
            (map (lambda (x) (eval-exp x env)) bodies)
            )
          )))


(define eval-let-bodies
  (lambda (bodies env)
      ; (display "eval-let-bodies\n")
      (if (null? (cdr bodies))
           ; (begin 
           ;  (display (car bodies))
           ;  ; (display (eval-exp (car bodies) env))
           ;  (display "\n")
            (eval-exp (car bodies) env)
          (begin 
            ; (display (car bodies))
            (eval-exp (car bodies) env)
            (eval-let-bodies (cdr bodies) env)))))

; evaluate the list of operands putting results into a list
(define improper-2-proper
  (lambda (ils)
    (if (pair? ils)
          (cons (car ils) (improper-2-proper (cdr ils)))
          (list ils))))

(define list-head
  (lambda (ls n)
    (if (eq? 0 n)
          '()
          (cons (car ls) (list-head (cdr ls) (sub1 n))))))

(define  eval-rands
  (lambda (rands env)
    (map (lambda (x) (eval-exp x env)) rands)))

;  Apply a procedure to its arguments.
;  At this point we only have primitive procedures.  
;  User-defined procedures will be added later.

(define apply-proc
  (lambda (proc-value args)
    ; (display "apply-proc\n")
    (cases proc-val proc-value
      [prim-proc (op) (apply-prim-proc op args)]
			; You will add other cases
      [proc (name)
        (name args)]
      [closure (id bodies env)
        (cond [(list? id)
                ; (display id)
                ; (display "\n")
                ; (display bodies)        
                    (let ((extended-env (extend-env 
                                                  id
                                                  args
                                                  env)))
                   (eval-let-bodies bodies extended-env))] ; need to apply procs somewhere, possibly here, possibly in eval-let-bodies, maybe elsewhere
              [(pair? id)
              ; (display args)
              ; (newline)

                  (let* ([prop-id (improper-2-proper id)]
                         [id-len (length prop-id)]
                         [extended-env (extend-env 
                                                    prop-id
                                                    (append (list-head args (sub1 id-len)) (list (list-tail args (sub1 id-len))))
                                                    env)])
                   (eval-let-bodies bodies extended-env))
                ]
             

              [(symbol? id)          
                    (let ((extended-env (extend-env 
                                                  (list id)
                                                  (list args)
                                                  env)))
                   (eval-let-bodies bodies extended-env))])]
      [else (eopl:error 'apply-proc
                   "Attempt to apply bad procedure: ~s" 
                    proc-value)])))

(define *prim-proc-names* '(+ - * / add1 sub1 cons = > < >= <= not and or car cdr list null? assq eq? equal? atom? zero? length list->vector 
  list? pair? procedure? vector->list vector make-vector vector-ref append eqv?
  vector? number? symbol? set-car! set-cdr! vector-set! display newline caar cadr cddr cdar caaar caadr cadar caddr cdaar cdadr cddar cdddr
  apply map quotient list-tail))

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
      [(quotient) (quotient (1st args) (2nd args))]
      [(add1) (+ (1st args) 1)]
      [(sub1) (- (1st args) 1)]
      [(cons) 
		(if (not (eq? 2 (length args)))
			(eopl:error 'apply-prim-proc "Incorrect number of arguments to cons: ~s" args)
			(cons (1st args) (2nd args)))]
      [(list-tail) (list-tail (1st args) (2nd args))]
      [(append) (append (1st args) (2nd args))]
      [(eqv?) (eqv? (1st args) (2nd args))]
      [(=) (= (1st args) (2nd args))]
      [(>=) (>= (1st args) (2nd args))]
      [(>) (> (1st args) (2nd args))]
      [(<) (< (1st args) (2nd args))]
      [(<=) (<= (1st args) (2nd args))]
      [(not) (not (1st args))]
      [(and) (andmap (lambda (x) x) args)]
      [(or) (ormap (lambda (x) x) args)]
      [(car) 
		(cond 
			[(not (eq? 1 (length args)))
				(eopl:error 'apply-prim-proc "Incorrect number of arguments to car: ~s" args)]
			[(not (list? (1st args)))
				(eopl:error 'apply-prim-proc "car requires a list: ~s" (1st args))]
			[(null? (1st args))
				(eopl:error 'apply-prim-proc "Cannot find the car of an empty list: ~s" (1st args))]
			[else
				(car (1st args))])]
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
      [(list?) (and (list? (1st args)) (not (proc-val? (1st args))))]
      [(pair?) (pair? (1st args))]
      [(procedure?) (or (procedure? (1st args)) (proc-val? (1st args)))]
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
		[(apply)
    (if (not (eq? 2 (length args)))
      (eopl:error 'apply-prim-proc "Incorrect number of arguments to apply: ~s" args)
      (apply-proc (1st args) (2nd args)))]
		[(map) (map (lambda x (apply-proc (1st args) x)) (2nd args))]
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
  (lambda (x) 
    (top-level-eval (syntax-expand (parse-exp x)))))









