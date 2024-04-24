; Andrew Coale
#lang plait

(define-type Value
  (numV [n : Number])
  (boolV [b : Boolean]) ;
  (closV [args : (Listof Symbol)]
         [body : Exp]
         [env : Env])
  (pairV [fst : Value]   ;
         [snd : Value])) ;

(define-type Exp
  (numE [n : Number])
  (boolE [b : Boolean]) ;
  (idE [s : Symbol])
  (plusE [l : Exp] 
         [r : Exp])
  (multE [l : Exp]
         [r : Exp])
  (equalsE [l : Exp]  ;
           [r : Exp]) ;
  (ifE [tst : Exp]  ;
       [thn : Exp]  ;
       [els : Exp]) ;
  (lamE [ns : (Listof Symbol)]      ; copied change from class
        [arg-types : (Listof Type)] ;
        [body : Exp])
  (appE [fun : Exp]
        [args : (Listof Exp)]) ;
  (pairE [frst : Exp]  ;
         [scnd : Exp]) ;
  (fstE [pr : Exp])    ;
  (sndE [pr : Exp]))   ;

(define-type Type
  (numT)
  (boolT)
  (arrowT [args : (Listof Type)]  ; later change to Listof Type
          [result : Type])
  (crossT [fst : Type]   ; pair type
          [snd : Type])) ;

(define-type Binding
  (bind [name : Symbol]
        [val : Value]))

(define-type-alias Env (Listof Binding))

(define-type Type-Binding
  (tbind [name : Symbol]
         [type : Type]))

(define-type-alias Type-Env (Listof Type-Binding))

(define mt-env empty)
(define extend-env cons)
(define extend-env-many append) ;

(module+ test
  (print-only-errors #t))

;; parse ----------------------------------------
(define (parse [s : S-Exp]) : Exp
  (cond
    [(s-exp-match? `NUMBER s) (numE (s-exp->number s))]
    [(s-exp-match? `true s) (boolE #t)]  ;
    [(s-exp-match? `false s) (boolE #f)] ;
    [(s-exp-match? `SYMBOL s) (idE (s-exp->symbol s))]
    [(s-exp-match? `{+ ANY ANY} s)
     (plusE (parse (second (s-exp->list s)))
            (parse (third (s-exp->list s))))]
    [(s-exp-match? `{* ANY ANY} s)
     (multE (parse (second (s-exp->list s)))
            (parse (third (s-exp->list s))))]
    [(s-exp-match? `{let {[SYMBOL : ANY ANY] ...} ANY} s) ; pluralized
     (let ([bs (map s-exp->list
                    (s-exp->list (second
                                  (s-exp->list s))))])
       (appE (lamE (map s-exp->symbol (map first bs))
                   (map parse-type (map third bs))
                   (parse (third (s-exp->list s))))
             (map parse (map fourth bs))))]
    [(s-exp-match? `{lambda {[SYMBOL : ANY] ...} ANY} s) ; added ellipses
     (let ([args (map s-exp->list                        ;
                      (s-exp->list                       ;
                       (second (s-exp->list s))))])      ;
       (lamE (map s-exp->symbol (map first args)) ;
             (map parse-type (map third args))
             (parse (third (s-exp->list s)))))]
    [(s-exp-match? `{= ANY ANY} s)              ;
     (equalsE (parse (second (s-exp->list s)))  ;
              (parse (third (s-exp->list s))))] ;
    [(s-exp-match? `{if ANY ANY ANY} s)      ;
     (ifE (parse (second (s-exp->list s)))   ;
          (parse (third (s-exp->list s)))    ;
          (parse (fourth (s-exp->list s))))] ;
    [(s-exp-match? `{pair ANY ANY} s)         ;
     (pairE (parse (second (s-exp->list s)))  ;
           (parse (third (s-exp->list s))))]  ;
    [(s-exp-match? `{fst ANY} s)              ;
     (fstE (parse (second (s-exp->list s))))] ;
    [(s-exp-match? `{snd ANY} s)              ;
     (sndE (parse (second (s-exp->list s))))] ;
    [(s-exp-match? `{ANY ANY ...} s)
     (appE (parse (first (s-exp->list s)))
           (map parse (rest (s-exp->list s))))]
    [else (error 'parse "invalid input")]))

(define (parse-type [s : S-Exp]) : Type
  (cond
   [(s-exp-match? `num s) 
    (numT)]
   [(s-exp-match? `bool s)
    (boolT)]
   [(s-exp-match? `(ANY ... -> ANY) s)
    (arrowT (map parse-type (reverse (rest (rest (reverse (s-exp->list s))))))
            (parse-type (third (s-exp->list s))))]
   [(s-exp-match? `(ANY * ANY) s)                  ;
    (crossT (parse-type (first (s-exp->list s)))   ;
            (parse-type (first (reverse (s-exp->list s)))))] ;
   [else (error 'parse-type "invalid input")]))

#;(module+ test
  (test (parse `2)
        (numE 2))
  (test (parse `x)
        (idE 'x))
  (test (parse `{+ 2 1})
        (plusE (numE 2) (numE 1)))
  (test (parse `{* 3 4})
        (multE (numE 3) (numE 4)))
  (test (parse `{+ {* 3 4} 8})
        (plusE (multE (numE 3) (numE 4))
               (numE 8)))
  #;(test (parse `{let {[x : num {+ 1 2}]}
                  y})
        (appE (lamE '(x) (numT) (idE 'y))
              (plusE (numE 1) (numE 2))))
  #;(test (parse `{lambda {[x : num]} 9})
        (lamE 'x (numT) (numE 9)))
  #;(test (parse `{double 9})
        (appE (idE 'double) (numE 9)))
  (test/exn (parse `{{+ 1 2}})
            "invalid input")

  (test (parse-type `num)
        (numT))
  (test (parse-type `bool)
        (boolT))
  #;(test (parse-type `(num -> bool))
        (arrowT (numT) (boolT)))
  (test/exn (parse-type `1)
            "invalid input"))

;; interp ----------------------------------------
(define (interp [a : Exp] [env : Env]) : Value
  (type-case Exp a
    [(numE n) (numV n)]
    [(boolE b) (boolV b)] ;
    [(idE s) (lookup s env)]
    [(plusE l r) (num+ (interp l env) (interp r env))]
    [(multE l r) (num* (interp l env) (interp r env))]
    [(equalsE l r) (num= (interp l env) (interp r env))] ; wrote num= 
    [(ifE tst thn els)      ;
     (if (equal? (interp tst env) (boolV #t))  ;
         (interp thn env)   ;
         (interp els env))] ;
    [(pairE frst scnd) (pairV (interp frst env) (interp scnd env))]              ;
    [(fstE pr) (type-case Value (interp pr env)                       ;
                 [(pairV frst scnd) frst] ;
                 [else (error 'interp "not a pair")])] ;
    [(sndE pr) (type-case Value (interp pr env)                       ;
                 [(pairV frst scnd) scnd] ;
                 [else (error 'interp "not a pair")])] ;
    [(lamE n t body)
     (closV n body env)]
    [(appE fun args) (type-case Value (interp fun env)
                       [(closV ns body c-env)
                        (interp body
                                (extend-env-many                             ;
                                 (map2 (lambda (n arg)                       ; changed, may be wrong
                                         (bind n (interp arg env))) ns args) ;
                                 c-env))]
                       [else (error 'interp "not a function")])]))

#;(module+ test
  (test (interp (parse `2) mt-env)
        (numV 2))
  (test/exn (interp (parse `x) mt-env)
            "free variable")
  (test (interp (parse `x) 
                (extend-env (bind 'x (numV 9)) mt-env))
        (numV 9))
  (test (interp (parse `{+ 2 1}) mt-env)
        (numV 3))
  (test (interp (parse `{* 2 1}) mt-env)
        (numV 2))
  (test (interp (parse `{+ {* 2 3} {+ 5 8}})
                mt-env)
        (numV 19))
  (test (interp (parse `{lambda {[x : num]} {+ x x}})
                mt-env)
        (closV 'x (plusE (idE 'x) (idE 'x)) mt-env))
  (test (interp (parse `{let {[x : num 5]}
                          {+ x x}})
                mt-env)
        (numV 10))
  (test (interp (parse `{let {[x : num 5]}
                          {let {[x : num {+ 1 x}]}
                            {+ x x}}})
                mt-env)
        (numV 12))
  (test (interp (parse `{let {[x : num 5]}
                          {let {[y : num 6]}
                            x}})
                mt-env)
        (numV 5))
  (test (interp (parse `{{lambda {[x : num]} {+ x x}} 8})
                mt-env)
        (numV 16))

  (test/exn (interp (parse `{1 2}) mt-env)
            "not a function")
  (test/exn (interp (parse `{+ 1 {lambda {[x : num]} x}}) mt-env)
            "not a number")
  (test/exn (interp (parse `{let {[bad : (num -> num) {lambda {[x : num]} {+ x y}}]}
                              {let {[y : num 5]}
                                {bad 2}}})
                    mt-env)
            "free variable"))

;; num+ and num* ----------------------------------------
(define (num-op [op : (Number Number -> Number)] [l : Value] [r : Value]) : Value
  (cond
   [(and (numV? l) (numV? r))
    (numV (op (numV-n l) (numV-n r)))]
   [else
    (error 'interp "not a number")]))
(define (num+ [l : Value] [r : Value]) : Value
  (num-op + l r))
(define (num* [l : Value] [r : Value]) : Value
  (num-op * l r))

(define (num= [l : Value] [r : Value]) : Value ;
  (cond
   [(and (numV? l) (numV? r))
    (boolV (= (numV-n l) (numV-n r)))]
   [else
    (error 'interp "not a number")]))

(module+ test
  (test (num+ (numV 1) (numV 2))
        (numV 3))
  (test (num* (numV 2) (numV 3))
        (numV 6)))

;; lookup ----------------------------------------
(define (make-lookup [name-of : ('a -> Symbol)] [val-of : ('a -> 'b)])
  (lambda ([name : Symbol] [vals : (Listof 'a)]) : 'b
    (type-case (Listof 'a) vals
      [empty (error 'find "free variable")]
      [(cons val rst-vals) (if (equal? name (name-of val))
                               (val-of (first vals))
                               ((make-lookup name-of val-of) name rst-vals))])))

(define lookup
  (make-lookup bind-name bind-val))

(module+ test
  (test/exn (lookup 'x mt-env)
            "free variable")
  (test (lookup 'x (extend-env (bind 'x (numV 8)) mt-env))
        (numV 8))
  (test (lookup 'x (extend-env
                    (bind 'x (numV 9))
                    (extend-env (bind 'x (numV 8)) mt-env)))
        (numV 9))
  (test (lookup 'y (extend-env
                    (bind 'x (numV 9))
                    (extend-env (bind 'y (numV 8)) mt-env)))
        (numV 8)))

;; typecheck ----------------------------------------
(define (typecheck [a : Exp] [tenv : Type-Env])
  (type-case Exp a
    [(numE n) (numT)]
    [(boolE b) (boolT)] ;
    [(plusE l r) (typecheck-nums l r tenv (numT))]
    [(multE l r) (typecheck-nums l r tenv (numT))]
    [(equalsE l r) (typecheck-nums l r tenv (boolT))] ;
    [(ifE tst thn els) (type-case Type (typecheck tst tenv)
                         [(boolT) (local [(define ttype (typecheck thn tenv))
                                          (define etype (typecheck els tenv))]
                                    (if (equal? ttype etype)
                                        ttype
                                        (type-error els (to-string ttype))))]
                         [else (type-error tst "bool")])] ;
    [(idE n) (type-lookup n tenv)]
    [(lamE ns arg-types body)
     (arrowT arg-types
             (typecheck body 
                        (extend-env-many      ;
                         (map2 tbind ns arg-types) ;
                         tenv)))]
    [(pairE frst scnd) (crossT (typecheck frst tenv) (typecheck scnd tenv))] ;
    [(fstE pr)
     (type-case Type (typecheck pr tenv)
       [(crossT fst snd) fst]
       [else (type-error pr "pair")])]
    [(sndE pr)
     (type-case Type (typecheck pr tenv)
       [(crossT fst snd) snd]
       [else (type-error pr "pair")])]
    [(appE fun args)
     (type-case Type (typecheck fun tenv)
       [(arrowT arg-types result-type)
        (if (typecheck-args arg-types args tenv)
            result-type
            (error 'typecheck "too many args"))]
       [else (type-error fun "function")])]))

(define (typecheck-nums l r tenv resultT) ; changed to pass in expected result type
  (type-case Type (typecheck l tenv)
    [(numT)
     (type-case Type (typecheck r tenv)
       [(numT) resultT] ;
       [else (type-error r "num")])]
    [else (type-error l "num")]))

(define (typecheck-args arg-types args tenv)
  (type-case (Listof Type) arg-types
    [(cons f r)
     (type-case (Listof Exp) args
       [(cons f-arg r-args)
        (if (equal? f (typecheck f-arg tenv))
            (typecheck-args r r-args tenv)
            (type-error f-arg (to-string f)))]
       [else (error 'typecheck "too few args")])]
    [else (empty? args)]))

#;(define (typecheck-if tst thn els tenv)           ; typechecking for ifE, ask if types of thn and els need to match
  (type-case Type (typecheck tst tenv)            ;
    [(boolT)                                      ;
     (type-case Type (typecheck thn tenv)         ;
       [(numT)                                    ;
        (type-case Type (typecheck els tenv)      ;
          [(numT) (numT)]                         ;
          [else (type-error els "num")])]         ;
       [(boolT)                                   ;
        (type-case Type (typecheck els tenv)      ;
          [(boolT) (boolT)]                       ;
          [else (type-error els "bool")])]        ;
       [(arrowT arg res)                          ;
        (type-case Type (typecheck els tenv)      ;
          [(arrowT arg2 res2) (arrowT arg2 res2)] ;
          [else (type-error els "arrow")])])]     ;
    [else (type-error tst "bool")]))              ;


(define (type-error a msg)
  (error 'typecheck (string-append
                     "no type: "
                     (string-append
                      (to-string a)
                      (string-append " not "
                                     msg)))))

(define type-lookup
  (make-lookup tbind-name tbind-type))

#;(module+ test
  (test (typecheck (parse `10) mt-env)
        (numT))
  (test (typecheck (parse `{+ 10 17}) mt-env)
        (numT))
  (test (typecheck (parse `{* 10 17}) mt-env)
        (numT))
  (test (typecheck (parse `{lambda {[x : num]} 12}) mt-env)
        (arrowT (numT) (numT)))
  (test (typecheck (parse `{lambda {[x : num]} {lambda {[y : bool]} x}}) mt-env)
        (arrowT (numT) (arrowT (boolT)  (numT))))

  (test (typecheck (parse `{{lambda {[x : num]} 12}
                            {+ 1 17}})
                   mt-env)
        (numT))

  (test (typecheck (parse `{let {[x : num 4]}
                             {let {[f : (num -> num)
                                      {lambda {[y : num]} {+ x y}}]}
                               {f x}}})
                   mt-env)
        (numT))

  (test/exn (typecheck (parse `{1 2})
                       mt-env)
            "no type")
  (test/exn (typecheck (parse `{{lambda {[x : bool]} x} 2})
                       mt-env)
            "no type")
  (test/exn (typecheck (parse `{+ 1 {lambda {[x : num]} x}})
                       mt-env)
            "no type")
  (test/exn (typecheck (parse `{* {lambda {[x : num]} x} 1})
                       mt-env)
            "no type"))

(module+ test ; part 1 tests
  (test (interp (parse `{if true 4 5})
                mt-env)
        (numV 4))
  (test (interp (parse `{if false 4 5})
                mt-env)
        (numV 5))
  (test (interp (parse `{if {= 13 {if {= 1 {+ -1 2}}
                                      12
                                      13}}
                            4
                            5})
                mt-env)
        (numV 5))
  (test (typecheck (parse `{= 13 {if {= 1 {+ -1 2}}
                                     12
                                     13}})
                   mt-env)
        (boolT))
  (test (typecheck (parse `{if {= 1 {+ -1 2}}
                               {lambda {[x : num]} {+ x 1}}
                               {lambda {[y : num]} y}})
                   mt-env)
        ;; This result may need to be adjusted after part 3:
        (arrowT (list (numT)) (numT)))
  (test/exn (typecheck (parse `{+ 1 {if true true false}})
                       mt-env)
            "no type"))

(module+ test
  (test (interp (parse `{pair 10 8})
                mt-env)
        ;; Your constructor might be different than pairV:
        (pairV (numV 10) (numV 8)))
  (test (interp (parse `{fst {pair 10 8}})
                mt-env)
        (numV 10))
  (test (interp (parse `{snd {pair 10 8}})
                mt-env)
        (numV 8))
  (test (interp (parse `{let {[p : (num * num) {pair 10 8}]}
                          {fst p}})
                mt-env)
        (numV 10))
  (test (typecheck (parse `{pair 10 8})
                   mt-env)
        ;; Your constructor might be different than crossT:
        (crossT (numT) (numT)))
  (test (typecheck (parse `{fst {pair 10 8}})
                   mt-env)
        (numT))
  (test (typecheck (parse `{+ 1 {snd {pair 10 8}}})
                   mt-env)
        (numT))
  (test (typecheck (parse `{lambda {[x : (num * bool)]}
                             {fst x}})
                   mt-env)
        ;; Your constructor might be different than crossT:
        (arrowT (list (crossT (numT) (boolT))) (numT)))
  (test (typecheck (parse `{{lambda {[x : (num * bool)]}
                              {fst x}}
                            {pair 1 false}})
                   mt-env)
        (numT))
  (test (typecheck (parse `{{lambda {[x : (num * bool)]}
                              {snd x}}
                            {pair 1 false}})
                   mt-env)
        (boolT))
  (test/exn (typecheck (parse `{fst 10})
                       mt-env)
            "no type")
  (test/exn (typecheck (parse `{+ 1 {fst {pair false 8}}})
                       mt-env)
            "no type")
  (test/exn (typecheck (parse `{lambda {[x : (num * bool)]}
                                 {if {fst x}
                                     1
                                     2}})
                       mt-env)
            "no type"))

(module+ test ; part 3 tests
  (test (interp (parse `{{lambda {}
                           10}})
                mt-env)
        (numV 10))
  (test (interp (parse `{{lambda {[x : num] [y : num]} {+ x y}}
                         10
                         20})
                mt-env)
        (numV 30))
  (test (typecheck (parse `{{lambda {[x : num] [y : bool]} y}
                            10
                            false})
                   mt-env)
        (boolT))
  (test/exn (typecheck (parse `{{lambda {[x : num] [y : bool]} y}
                                false
                                10})
                       mt-env)
            "no type"))

(module+ test ; extra tests
  (test (interp (parse `{* 3 4}) mt-env)
        (numV 12))
  (test/exn (parse `()) "invalid input")
  (test (parse-type `{num -> bool})
        (arrowT (list (numT)) (boolT)))
  (test/exn (parse-type `l) "invalid input")
  (test/exn (interp (parse `(fst 1)) mt-env) "not a pair")
  (test/exn (interp (parse `(snd 1)) mt-env) "not a pair")
  (test/exn (interp (appE (numE 1) (list (numE 2))) mt-env) "not a function")
  (test/exn (num-op + (boolV #t) (numV 1)) "not a number")
  (test/exn (num= (boolV #t) (numV 1)) "not a number")
  (test/exn (typecheck (ifE (boolE #t) (numE 1) (boolE #f)) mt-env) "no type: (boolE #f) not (numT)")
  (test (typecheck (multE (numE 1) (numE 2)) mt-env) (numT))
  (test/exn (typecheck (sndE (numE 1)) mt-env) "no type: (numE 1) not pair")
  (test/exn (typecheck (appE (numE 1) (list (numE 2))) mt-env) "no type: (numE 1) not function")
  (test/exn (typecheck-nums (boolE #t) (numE 1) mt-env numV) "no type: (boolE #t) not num")
  (test/exn (typecheck (parse `{{lambda {[x : num]} x} 2 1}) mt-env) "too many args")
  (test/exn (typecheck (parse `{{lambda {[x : num] [y : num]} x} 2}) mt-env) "too few args"))