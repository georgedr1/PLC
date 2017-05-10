;:  Single-file version of the interpreter.
;; Easier to submit to server probably harder to use in the development process

 (load "C:/Users/kildufje/Documents/School/Senior/Spring/CSSE304/PLC/chez-init.ss")
;(load "C:/Users/georgedr/Documents/Class stuff/Spring 16-17/PLC/PLC/chez-init.ss")

;Things to convert to cps: eval-exp, set!-in-env, make a new eval-bodies-cps, map-cps, eval-rands, apply-proc, extend-env, extend-env-recrusively

;-------------------+
;                   |
;    DATATYPES      |
;                   |
;-------------------+

; parsed expression

(define-datatype expression expression?
  [or-exp
    (args (list-of expression?))]
  [exit-list-exp
    (args (list-of expression?))]
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
  [define-exp
    (variable symbol?)
    (definition expression?)]
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
   (vals (list-of box?))
   (env environment?))
  [recursively-extended-env-record
    (proc-names (list-of symbol?))
    (idss (lambda (x) (or ((list-of list?) x) ((list-of pair?) x))))
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

(define-datatype continuation continuation?
  [test-k
    (then-exp expression?)
    (else-exp expression?)
    (env environment?)
    (k continuation?)]
  [rator-k 
    (rands (list-of? expression?))
    (env environment?)
    (k continuation?)]
  [rands-k 
    (proc-value scheme-value?)
    (k continuation?)] 
  )
	 
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

(define parse-exp         
  (lambda (datum)
    (cond
     [(symbol? datum) (var-exp datum)]
     [(pair? datum)
      (cond
        [(eqv? (car datum) 'define)
          (define-exp (cadr datum) (parse-exp (caddr datum)))]
        [(eqv? (car datum) 'exit-list)
          (exit-list-exp (map parse-exp (cdr datum)))]
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
      [(eqv? (car datum) 'or)
        (or-exp (map parse-exp (cdr datum)))]
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
    (extended-env-record syms (map box vals) env)))

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
    				(succeed (list-ref (map unbox vals) pos))
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
          [define-exp (variable definition)
            (define-exp variable (syntax-expand definition))]
          [var-exp (id) exp]
          [lit-exp (id) exp]
          [app-exp (rator rands) (app-exp rator (map syntax-expand rands))]
          [or-exp (args)
            (or-exp (map syntax-expand args))]
          [exit-list-exp (args)
            (exit-list-exp (map syntax-expand args))]
          [lambda-exp (id body) 
            (lambda-exp id (map syntax-expand body))]
          [let-exp (vars body)
            (app-exp 
              (lambda-exp (map car vars) (map syntax-expand body))
              (map syntax-expand (map cadr vars)))]
          [let*-exp (vars body)
            ; (display vars)
            ; (newline)
            ; (display (map cadadr vars))
            ; (newline)
            ; (display (map caaddr vars))
            ; (newline)
            (syntax-expand (expand-let* (map cadadr vars) (map caaddr vars) body))]
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
            (begin-exp (map syntax-expand body))]
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


(define expand-let*
    (lambda (var sym body)
      (if (null? (cdr var))
        (let-exp (list (list (car var) (car sym))) body)
        (let-exp (list (list (car var) (car sym))) (list (expand-let* (cdr var) (cdr sym) body))))))



;-------------------+
;                   |
;        CPS        |
;                   |
;-------------------+


(define map-cps
  (lambda (f ls k)
    (if (null? ls)
      (k '())
      (f (car ls) (lambda (v) (map-cps f (cdr ls) (lambda (v2) (k (cons v v2 )))))))))

(define apply-k
  (lambda (k val)
    (cases continuation k
      [test-k (then-exp else-exp env k)
        (if val
          (eval-exp then-exp env k)
          (eval-exp else-exp env k))]
      [rator-k (rands env k)
        (eval-rands rands env (rands-k val k) k)]
      [rands-k (proc-value k)
        (apply-proc proc-value val k)]))) 


;-------------------+
;                   |
;    INTERPRETER    |
;                   |
;-------------------+



; top-level-eval evaluates a form in the global environment

(define top-level-eval
  (lambda (form)
    ; later we may add things that are not expressions.
    (cases expression form
      [begin-exp (body)
        (top-level-begin body)]
      [define-exp (variable definition)
        (extend-global-env variable definition)]
      [exit-list-exp (expressions)
        (display "exit-list\n")]
      [else 
        (eval-exp form global-env (lambda (v) v))])))

(define top-level-begin
  (lambda (body)
    (if (null? (cdr body))
          (top-level-eval (car body))
          (begin
                (top-level-eval (car body))
                (top-level-begin (cdr body))))))

(define extend-global-env 
  (lambda (variable definition)
    ;(display global-env)
    (newline)
    (cases environment global-env
      [extended-env-record (syms vals env)
        (set! global-env (extend-env (list variable) (list (top-level-eval definition)) global-env))
        ; (set! syms (cons variable syms))
        ; (set! vals (cons (box definition) vals))
       ; (display global-env)
    (newline)]
      [else 
        (display "not ready")])))

; eval-exp is the main component of the interpreter

(define eval-exp
  (lambda (exp env k)
    ; (display "eval-exp\n")
    ; (display env)
    ; (display "\n")
    (cases expression exp
      [lit-exp (datum) (apply-k k datum)]
      [var-exp (id)
				(apply-env env 
                   id; look up its value.
      	           (lambda (x) x) ; procedure to call if it is in the environment 
                   (lambda () (apply-env global-env
                                         id
                                         (lambda (x) x) 
                                         (lambda () (error 'apply-env
                                                            "variable ~s is not bound"
                                                            id)))))] 
      [or-exp (args)
        (cond [(null? (cdr args)) (eval-exp (car args) env k)]
              [(eval-exp (car args) env k) #t]
              [else (eval-exp (or-exp (cdr args)) env k)])]    
      [app-exp (rator rands)
        (let ([proc-value (eval-exp rator env k)]
              [args (eval-rands rands env k)])
            (apply-proc proc-value args k))]
      [if-exp (condition body)
        (if (eval-exp condition env k)
              (eval-exp (car body) env k)
              (if (not (null? (cdr body)))
                    (eval-exp (cadr body) env k)))]
      [let-exp (vars body)
        (let ((extended-env (extend-env 
                                      (map car vars)
                                      (map (lambda (x) (eval-exp x env k)) (map cadr vars))
                                      env)))
          (eval-bodies body extended-env k))]
      [letrec-exp (ids bodies)
        (eval-bodies bodies
          (extend-env-recursively (map cadadr ids) (map cadr (map caaddr ids)) (map caddr (map caaddr ids)) env) k)]
      [begin-exp (bodies)
        (eval-bodies bodies env k)]
      [lambda-exp (id body)
       ; (display env)
        (closure id body env)
        ]
         [set!-exp (var new)
          (let ([new-val (eval-exp new env k)])
                (set!-in-env var new-val env)
            )]
      [else (eopl:error 'eval-exp "Bad abstract syntax: ~a" exp)])))


(define set!-in-env 
  (lambda (var new-val env)
    (cases environment env       ;  succeed is appluied if sym is found otherwise 
      [empty-env-record ()       ;  fail is applied.
        (eopl:error 'set!-in-env "var not found in empty environment: ~a" var)]
      [extended-env-record (syms vals next-env)
        (let ([pos (list-find-position (cadr var) syms)])
                (if (number? pos)
                        (let ([old-val (list-ref vals pos)])
                          (set-box! old-val new-val))
                        (set!-in-env var new-val next-env)))]
      [recursively-extended-env-record (proc-names idss bodiess next-env)
        (let ([pos (list-find-position (cadr var) proc-names)])
                (if (number? pos)
                        (let ([old-val (list-ref idss pos)])
                          (set-box! old-val new-val))
                        (set!-in-env var new-val next-env)))]
      [else
        (eopl:error 'set!-in-env "wrong env: ~a" var)])))


(define eval-bodies
  (lambda (bodies env k)
      (if (null? (cdr bodies))
            (eval-exp (car bodies) env k)
          (begin 
            (eval-exp (car bodies) env k)
            (eval-bodies (cdr bodies) env k)))))

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
  (lambda (rands env k)
    (map (lambda (x) (eval-exp x env k)) rands)))

;  Apply a procedure to its arguments.
;  At this point we only have primitive procedures.  
;  User-defined procedures will be added later.

(define apply-proc
  (lambda (proc-value args k)
    ; (display "apply-proc\n")
    (cases proc-val proc-value
      [prim-proc (op) (apply-prim-proc op args k)]
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
                   (eval-bodies bodies extended-env k))] ; need to apply procs somewhere, possibly here, possibly in eval-bodies, maybe elsewhere
              [(pair? id)
              ; (display args)
              ; (newline)

                  (let* ([prop-id (improper-2-proper id)]
                         [id-len (length prop-id)]
                         [extended-env (extend-env 
                                                    prop-id
                                                    (append (list-head args (sub1 id-len)) (list (list-tail args (sub1 id-len))))
                                                    env)])
                   (eval-bodies bodies extended-env k))
                ]
             

              [(symbol? id)          
                    (let ((extended-env (extend-env 
                                                  (list id)
                                                  (list args)
                                                  env)))
                   (eval-bodies bodies extended-env k))])]
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

(define global-env init-env)

; Usually an interpreter must define  each 
; built-in procedure individually.  We are "cheating" a little bit.

(define apply-prim-proc
  (lambda (prim-proc args k)
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
      ; [(or) (apply-or args)]
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
      (apply-proc (1st args) (2nd args) k))]
		[(map) (map (lambda x (apply-proc (1st args) x k)) (2nd args))]
      [else (error 'apply-prim-proc 
            "Bad primitive procedure name: ~s" 
            prim-proc)])))

(define apply-or
  (lambda (args)
    (cond [(null? args) #f]
          [(car args) #t]
          [else (apply-or (cdr args))])))
			
	

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


(define reset-global-env
 (lambda () (set! global-env init-env)))






