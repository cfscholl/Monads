#lang racket

; Give me an M give me an O ...
;   __  __    U  ___ u  _   _       _      ____    ____     
; U|' \/ '|u   \/"_ \/ | \ |"|  U  /"\  u |  _"\  / __"| u  
; \| |\/| |/   | | | |<|  \| |>  \/ _ \/ /| | | |<\___ \/   
;  | |  | |.-,_| |_| |U| |\  |u  / ___ \ U| |_| |\u___) |   
;  |_|  |_| \_)-\___/  |_| \_|  /_/   \_\ |____/ u|____/>>  
; <<,-,,-.       \\    ||   \\,-.\\    >>  |||_    )(  (__) 
;  (./  \.)     (__)   (_")  (_/(__)  (__)(__)_)  (__)
;
; Implemenation of a monadic interpreter as defined in:
; The essence of functional prorgamming
; Philip Wadler, University of Glasgow
; (https://cs.uwaterloo.ca/~david/cs442/monads.pdf)

; If you have remarks or questions about this
; implementation please contact me
; at Christophe.Scholliers@UGent.be

; The first thing we do is define the terms of our language
; We define the terms of the language as structures
; Term ::= Var Name | (Con Int) | (Lam  n Term) | (App Term Term)
(struct Var  (Name       )  #:transparent)
(struct Con  (Int        )  #:transparent)
(struct Add  (Term1 Term2)  #:transparent)
(struct Lam  (Name  Term )  #:transparent)
(struct App  (Term1 Term2)  #:transparent)


; Then we define the values of our language
; also as structures
; Value ::= Wrong | Num Int | Fun f
(struct Wrong (    )  #:transparent)
(struct Num   (Int )  #:transparent)
(struct Fun   (Fun )  #:transparent)

; We represent environments as associations lists

; Looking up a value in the environment
; either returns a value or if the variable is not
; found in the environment returns wrong
(define (lookup x env)
  (let ((search (assoc x env)))
    (if (empty? search)
        (Wrong)
        (cdr search))))

; Extending the environment is just consing the new pair
; to the front of the association list
(define (extend-env x v env) (cons (cons x v) env))

; Finally we implement an interp function for our language
(define (interp term env)
  (cond
    ((Var? term) (lookup (Var-Name term) env))
    ((Con? term) (Num (Con-Int term)))
    ((Add? term) (add (interp (Add-Term1 term) env)
                      (interp (Add-Term2 term) env)))
    ((Lam? term) (Fun (lambda (a) (interp (Lam-Term term) (extend-env (Lam-Name term) a env)))))
    ((App? term) (apply (interp (App-Term1 term) env)
                        (interp (App-Term2 term) env)))))

; Adding only works when both terms are number values
(define (add t1 t2)
  (if (and (Num? t1) (Num? t2))
      (Num (+ (Num-Int t1) (Num-Int t2)))
      (Wrong)))

; Applying a function only works if the first argument is a
; function
(define (apply t1 t2)
  (if (Fun? t1)
      ((Fun-Fun t1) t2)
      (Wrong)))

; We try out our interpreter and see things are working :)
(interp (App (Lam 'x (Add (Var 'x) (Var 'x))) (Add (Con 1) (Con 2))) '())


;---------------------------------------------------------------------------------------------

; We now reimplement our interpreter in monadic style.
; In racket we can define it as a structure with two fields
; unit :: a   -> M a
; bind :: M a -> a -> M b -> M b
(struct monad (unit bind)   #:transparent)

; We define two dummy procedures unitM and bindM
; a -> M a
(define unitM empty)
; M a -> a -> M b -> M b
(define bindM empty)

; Given a monad structure we set unitM and bindM to
; that monadgh
(define (setMonad! m)
  (set! unitM (monad-unit m))
  (set! bindM (monad-bind m)))

; The monadic interpreter
; term -> environment -> M value
(define (interp/m term env)
  (cond
    ((Var? term) (lookup/m (Var-Name term) env))
    ; We need to return a M value
    ; so we have to apply unitM 
    ((Con? term) (unitM (Num (Con-Int term))))
    ; 
    ((Add? term) (bindM
                  (interp/m (Add-Term1 term) env)
                  (lambda (a) (bindM
                               (interp/m (Add-Term2 term) env)
                               (lambda (b) (add/m a b)))))

                 )
    ((Lam? term) (unitM (Fun (lambda (a)
                        (interp/m (Lam-Term term)
                                  (extend-env (Lam-Name term) a env))))))
    ((App? term) (bindM
                   (interp/m (App-Term1 term) env)
                   (lambda (f)
                     (bindM
                      (interp/m (App-Term2 term) env)
                      (lambda (a) (apply/m f a))))))))

(define (add/m t1 t2)
  (if (and (Num? t1) (Num? t2))
      (unitM (Num (+ (Num-Int t1) (Num-Int t2))))
      (unitM (Wrong))))

(define (apply/m t1 t2)
  (if (Fun? t1)
      ((Fun-Fun t1) t2)
      (unitM (Wrong))))

; Looking up a value in the environment
(define (lookup/m x env)
  (let ((search (assoc x env)))
    (if (empty? search)
        (unitM (Wrong))
        (unitM (cdr search)))))


(define IdentityMonad (monad identity (lambda (a k) (k a))))

(define StateMonad (monad (lambda (a)
                            (lambda (s0)
                              (cons a s0)))
                          
                          (lambda (m k)
                            (lambda (s0)
                              (let ((r1 (m s0)))
                                ((k (car r1)) (cdr r1)))))))
                                

(setMonad! IdentityMonad)

(interp/m (App (Lam 'x (Add (Var 'x) (Var 'x))) (Add (Con 9) (Con 2))) '())

(setMonad! StateMonad)

(define result (interp/m (App (Lam 'x (Add (Var 'x) (Var 'x))) (Add (Con 9) (Con 2))) '()))
(define result1  (interp/m (Add (Con 9) (Con 2)) '()))
(define x (bindM (unitM (Wrong)) (lambda (b) (unitM (Wrong)))))