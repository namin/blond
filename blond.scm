;;; From mcvax!diku.dk!danvy@uunet.UU.NET Wed Nov 16 20:38:55 1988
;;; Date:  Thu, 6 Oct 88 15:49:55 +0100
;;; From: mcvax!diku.dk!danvy@uunet.UU.NET (Olivier Danvy)
;;; To: scheme-librarian@zurich.ai.mit.edu
;;; Subject: submission
;;; 
;;; 
;;; 	Dear librarian,
;;; 
;;; 	here is the source code for the Blond reflective tower
;;; 	as described in the article "Intensions and Extensions
;;; 	in a Reflective Tower", at the LFP'88 conference.
;;; 	Would you find it convenient to have the LaTex source
;;; 	of the manual (25 pages), too?
;;; 
;;; 	Keep in touch.
;;; 
;;; 		Kind regards,		Olivier
;;; 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; blond-88.scm -- commented listing of Blond in -*- Scheme -*- version 0.8
;
;
; This is the non-reflective simulator of a reflective tower described in
;
;               Intensions and Extensions in a Reflective Tower
;
; pp 327-341 of the proceedings of the
;           1988 ACM Conference on Lisp and Functional Programming
;
;
;                                       Olivier Danvy & Karoline Malmkjaer
;                                       DIKU -- Computer Science Department
;                                       University of Copenhagen
;                                       Universitetsparken 1
;                                       DK-2100 Copenhagen O
;                                       Denmark
;
;                                       e-mail: danvy@diku.dk
;                                               karoline@diku.dk
;                                       from US: mcvax!diku!danvy@uunet.uu.net
;
;                                       Phone: (45) 1 39 64 66 and ask
; -----------------------------------------------------------------------------


;                                               Copenhagen, January-August 1988

; Use: under Scheme, load "blond.scm"
; then type (blond)

; This interpreter is totally meta-circular.
; It can be loaded in a blond session with
;       (load "blond.scm")
; and started with
;       (blond)
; at the price of a certain slowness,
; but starting a reflective tower orthogonal to the current one.
;
; Note: as it stands here, Blond is not perfect, and has already been
; considerably improved. But it has the advantage to be faithful
; to the LFP'88 paper and to have an accurate manual.
; -----------------------------------------------------------------------------


; Domains:

; Denotable values = expressible values = storable values:
; Val = Num + String + Ide + Pair +
;       Abstraction + Subr + Fsubr +
;       Environment + Continuation +
;       DeltaReifier + GammaReifier

; Answers:
; Ans = Val + {_|_}

; Meta-continuations:
; Meta-Cont = (Env x Cont) x Meta-Cont

; Environments and continuations:
; Env = (Ide* x Val*)*          -- lexical extensions, then global, then common
; Cont = Val x MC -> Ans

; Procedures, primitive functions and control structures:
; Lambda-Abstraction =  Val* x Cont x MC -> Ans
; Subr = Val* -> Val
; Fsubr = Expr* x Env x Cont  x MC

; Reified environments and continuations:
; Environment = (Unit -> Val) + (Ide -> Val) + (Ide x Val -> Val)
; Continuation = Cont

; Reifiers:
; Delta-Reifier = Val x Val x Val x Env x Cont x MC -> Ans
; Gamma-Reifier = Val x Val x Val x Cont x MC -> Ans


; ----- the core --------------------------------------------------------------
; A Blond expression is either a constant (that are left as they are),
; an identifier (that is looked up) or a pair (that represents a redexe).

; Expr * Env * Cont * Meta-Cont -> Val
(define _eval
    (lambda (e r k tau)
        (cond
            ((_constant? e)
                (k e tau))
            ((_identifier? e)
                (_lookup e r k tau))
            ((pair? e)
                (_eval (car e)
                       r
                       (lambda (f tau)
                           (_apply f (cdr e) r k tau))
                       tau))
            (else
                 (_wrong '_eval "unknown form" e)))))


; An identifier is first looked up in the current lexical extension of
; the environment, then in the global environment of the current level,
; and lastly in the common environment.

; Ide * Env * Cont * Meta-Cont -> Val
(define _lookup
    (lambda (i r k tau)
        (let ((pos (_index i (caar r))))
            (if (isNatural? pos)
                (k (_access (_nth pos (cdar r))) tau)
                (if (null? (cdr r))
                    (_lookup_common i k tau)
                    (_lookup i (cdr r) k tau))))))

; Ide * Cont * Meta-Cont -> Val
(define _lookup_common
    (lambda (i k tau)
        (let ((pos (_index i table-common-identifiers)))
            (if (isNatural? pos)
                (k (_access (_nth pos table-common-values)) tau)
                (_wrong '_lookup_common "unbound identifier" i)))))


; Applying an applicable object dispatches on its injection tag.

; Fun * List-of-Expr * Env * Cont * Meta-Cont -> Val
(define _apply
    (lambda (fo l r k tau)
        (if (_applicable? fo)
            (case (_fetch-ftype fo)
                ((subr)
                    (_apply_subr fo l r k tau))
                ((fsubr)
                    (_apply_fsubr fo l r k tau))
                ((lambda-abstraction)
                    (_apply_procedure fo l r k tau))
                ((delta-abstraction)
                    (_apply_delta-reifier fo l r k tau))
                ((gamma-abstraction)
                    (_apply_gamma-reifier fo l r k tau))
                ((environment)
                    (_apply_environment fo l r k tau))
                ((continuation)
                    (_apply_continuation fo l r k tau))
                (else
                     (_wrong '_apply "unknown functional object" (car fo))))
            (_wrong '_apply "unapplicable form" fo))))


; Applying a primitive function dispatches on its arity. There are
; currently nullary, unary, binary, and ternary primitive functions.

; Subr * List-of-Expr * Env * Cont * Meta-Cont -> Val
(define _apply_subr
    (lambda (f l r k tau)
        (if (not (= (length l) (_fetch-arity f)))
            (_wrong '_apply_subr "arity mismatch" l)
            (case (_fetch-arity f)
                (0
                    (k ((_fetch-value f)) tau))
                (1
                    (_eval (car l) r (lambda (a tau)
                                         (k ((_fetch-value f) a) tau)) tau))
                (2
                    (_eval (car l)
                           r
                           (lambda (a1 tau)
                               (_eval (cadr l)
                                      r
                                      (lambda (a2 tau)
                                          (k ((_fetch-value f) a1 a2) tau))
                                      tau))
                           tau))
                (3
                    (_eval (car l)
                           r
                           (lambda (a1 tau)
                               (_eval (cadr l)
                                      r
                                      (lambda (a2 tau)
                                          (_eval (caddr l)
                                                 r
                                                 (lambda (a3 tau)
                                                     (k ((_fetch-value f)
                                                            a1 a2 a3) tau))
                                                 tau))
                                      tau))
                           tau))
                (else
                    (_wrong '_apply_subr "arity" f))))))


; Before reducing a special form, its arity is checked.

; Fsubr * List-of-Expr * Env * Cont * Meta-Cont -> Val
(define _apply_fsubr
    (lambda (fv l r k tau)
        (if (or (= (length l) (_fetch-arity fv))
                (zero? (_fetch-arity fv)))      ; arbitrary number of arguments
            ((_fetch-value fv) l r k tau)
            (_wrong '_apply_fsubr "arity mismatch" l))))


; The arity of procedures is also checked:

; Lambda-Abstraction * List-of-Expr * Env * Cont * Meta-Cont -> Val
(define _apply_procedure
    (lambda (p l r k tau)
        (if (not (= (length l) (_fetch-arity p)))
            (_wrong '_apply_procedure "arity mismatch" l)
            (_evlis l r (lambda (lv tau)
                            ((_fetch-value p) lv k tau)) tau))))


; A sequence of expressions is evaluated from left to right:

; List-of-Expr * Env * Cont * Meta-Cont -> Val
(define _evlis
    (lambda (l r k tau)
        (if (null? l)
            (k () tau)
            (_eval (car l)
                   r
                   (lambda (v tau)
                       (_evlis (cdr l)
                               r
                               (lambda (lv tau)
                                   (k (cons v lv) tau))
                               tau))
                   tau))))


; Applying a reified environment gives access to its representation,
; looks up an identifier, or assigns it, according to the number of arguments.

; Reified-Env * List-of-Expr * Env * Cont * Meta-Cont -> Val
(define _apply_environment
    (lambda (f l r k tau)
        (case (length l)
            (0
                (k (_env-down f) tau))
            (1
                (_eval (car l)
                       r
                       (lambda (i tau)
                           (if (_identifier? i)
                               (k (_R_lookup i (_env-down f)) tau)
                               (_wrong '_apply_environment
                                       "not an identifier"
                                       i)))
                       tau))
            (2
                (_eval (car l)
                       r
                       (lambda (i tau)
                           (_eval (cadr l)
                                  r
                                  (lambda (v tau)
                                      (_apply_environment_set! i v f k tau))
                                  tau))
                       tau))
            (else
                 (_wrong '_apply_environment "arity mismatch" l)))))


; Ide * Reified-Env -> Val
(define _R_lookup
    (lambda (i r)
        (let ((pos (_index i (caar r))))
            (if (isNatural? pos)
                (_access (_nth pos (cdar r)))
                (if (null? (cdr r))
                    (_R_lookup_common i)
                    (_R_lookup i (cdr r)))))))

; Ide -> Val
(define _R_lookup_common
    (lambda (i)
        (let ((pos (_index i table-common-identifiers)))
            (if (isNatural? pos)
                (_access (_nth pos table-common-values))
                '***undefined***))))


; Ide * Val * Reified-Env * Cont * Meta-Cont -> Val
(define _apply_environment_set!
    (lambda (i v f k tau)
        (if (_identifier? i)
            (let ((location (_L_lookup i (_env-down f))))
                (if (null? location)
                    (_wrong '_apply_environment "undefined variable" i)
                    (let ((o (_access location)))
                        (begin
                            (_update location v)
                            (k o tau)))))
            (_wrong '_apply_environment "not an identifier" i))))

; Ide * Reified-Env -> Loc
(define _L_lookup
    (lambda (i r)
        (let ((pos (_index i (caar r))))
            (if (isNatural? pos)
                (_nth pos (cdar r))
                (if (null? (cdr r))
                    (_L_lookup_common i r)
                    (_L_lookup i (cdr r)))))))

; Ide * Reified-Environment -> Loc
(define _L_lookup_common
    (lambda (i r)
        (let ((pos (_index i table-common-identifiers)))
            (if (isNatural? pos)
                (begin
                    (set-car! (car r)
                              (cons i (caar r)))
                    (set-cdr! (car r)
                              (cons (_access (_nth pos table-common-values))
                                    (cdar r)))
                    (cdar r))
                '()))))


; Applying a continuation can be done jumpily or pushily. In the first case,
; the current continuation is ignored; in the second, the current
; environment and continuation are pushed onto the meta-continuation.

; Reified-Cont * List-of-Expr * Env * Cont * Meta-Cont -> Val
(define _apply_continuation-jumpy
    (lambda (c l r k tau)
        (if (= (length l) 1)
            (_eval (car l) r (_cont-down c) tau)
            (_wrong '_apply_continuation-jumpy "arity mismatch" l))))

; Reified-Cont * List-of-Expr * Env * Cont * Meta-Cont -> Val
(define _apply_continuation-pushy
    (lambda (c l r k tau)
        (if (= (length l) 1)
            (_eval (car l) r (_cont-down c) (_meta-push r k tau))
            (_wrong '_apply_continuation-pushy "arity mismatch" l))))

; Hook for the toggle switch-continuation-mode:
(define _apply_continuation _apply_continuation-jumpy)



; Applying a reifier reifies its arguments, the current environment and
; the current continuation:

; Delta-Reifier * List-of-Expr * Env * Cont * Meta-Cont -> Val
(define _apply_delta-reifier
    (lambda (d l r k tau)
        ((_untag d) (_exp-up* l) (_env-up r) (_cont-up k)
                    (_top-env tau) (_top-cont tau) (_meta-pop tau))))


; Gamma-Reifier * List-of-Expr * Env * Cont * Meta-Cont -> Val
(define _apply_gamma-reifier
    (lambda (g l r k tau)
        ((_untag g) (_exp-up* l) (_env-up r) (_cont-up k)
                    (_top-cont tau) (_meta-pop tau))))


; List-of-Expr -> List-of-Exp
(define _exp-up*
    (lambda (l)         ; (map copy l)
        l))

(define _exp-up
    (lambda (e)
        e))             ; (copy e)

; Env -> Reified-Env
(define _env-up
    (lambda (r)
        (cons 'environment (lambda () r))))

; Cont -> Reified-Cont
(define _cont-up
    (lambda (k)
        (cons 'continuation k)))

(define _untag cdr)



; Reflecting spawns a new level.

; List-of-Expr * Env * Cont * Meta-Cont -> Val
(define _meaning
    (lambda (l r k tau)
        (_eval (car l)
               r
               (lambda (a1 tau)
                   (_eval (cadr l)
                          r
                          (lambda (a2 tau)
                              (_eval (caddr l)
                                     r
                                     (lambda (a3 tau)
                                         (_check_and_spawn a1 a2 a3 r k tau))
                                     tau))
                          tau))
               tau)))

; Val * Val * Val * Env * Cont * Meta-Cont -> Val
(define _check_and_spawn
    (lambda (a1 a2 a3 r k tau)
        (cond
            ((not (_expressible? a1))
                (_wrong '_meaning "non-expressible value" a1))
            ((not (_ecological? a2))
                (_wrong '_meaning "polluted environment" a2))
            ((not (_continuable? a3))
                (_wrong '_meaning "pitfall" a3))
            (else
                (_spawn (_exp-down a1) (_env-down a2)
                        a3      ; _spawn is going to _cont-down a3
                        r k tau)))))

; Expr -> Bool
(define _expressible?           ; safe
    (lambda (x)
        (or (constant? x)
            (_identifier? x)
            (and (pair? x)
                (_expressible? (car x))
                (or (null? (cdr x))
                    (and (pair? (cdr x))
                        (_expressible? (cdr x))))))))

; Expr -> Bool
(define _expressible?           ; cheaper
    (lambda (x)
        'true))

; Reified-Env -> Bool
(define _environment?           ; naive: one could build such an "environment"
    (lambda (x)                 ; changing the tag of a reified continuation!
        (and (pair? x)          ; he would certainly have what he deserves
            (equal? (car x) 'environment)
            (procedure? (cdr x)))))

(define _ecological? _environment?)

; Expr -> Bool
(define _continuable?
    (lambda (x)
        (and (_applicable? x)
            (case (_fetch-ftype x)
                ((subr)
                    (= (_fetch-arity x) 1))
                ((fsubr)
                    (= (_fetch-arity x) 1))
                ((lambda-abstraction)
                    (= (_fetch-arity x) 1))
                ((delta-abstraction gamma-abstraction environment continuation)
                    #t)
                (else
                    #f)))))

; Expr -> Expr
(define _exp-down
    (lambda (x)
        x))

; Reified-Env -> Env
(define _env-down
    (lambda (r)
        (_unwrap-env (cdr r))))

; Reified-Env-without-injection-tag -> Env
(define _unwrap-env
    (lambda (r)
        (r)))

; Expr -> Cont
(define _cont-down cdr)




; Expr * Env * Cont * Env * Cont * Meta-Cont -> Val
(define _spawn
    (lambda (_e _r _k r k tau)
        (case (_fetch-ftype _k)
            (subr
                (_eval _e
                      _r
                      (lambda (a tau)
                          (_terminate-level ((_fetch-value _k) a) tau))
                      (_meta-push r k tau)))
            (fsubr              ; adventurous
                ((_fetch-value _k)
                     (list _e) _r _terminate-level (_meta-push r k tau)))
            (lambda-abstraction
                (_eval _e
                       _r
                       (lambda (a tau)
                           ((_fetch-value _k) (list a)
                                             (_top-cont tau)
                                             (_meta-pop tau)))
                       (_meta-push r k tau)))
            (delta-abstraction
                ((_untag d) (_exp-up _e) (_env-up _r)
                            (_cont-up _terminate-level)
                            r k tau))
            (gamma-abstraction
                ((_untag g) (_exp-up _e) (_env-up _r)
                            (_cont-up _terminate-level)
                            k tau))
            (environment
                (_eval _e
                       _r
                       (lambda (i tau)
                           (if (_identifier? i)
                               (_terminate-level (_R_lookup i
                                                            (_env-down _k))
                                                 tau)
                               (_wrong '_environment
                                       "not an identifier"
                                       i)))
                       (_meta-push r k tau)))
            (continuation
                (_eval _e _r (_cont-down _k) (_meta-push r k tau))))))



; Terminating a level transmits the result to the level above:

; Val * Meta-Cont -> Val
(define _terminate-level
    (lambda (a tau)
        ((_top-cont tau) a (_meta-pop tau))))


; An applicable object is built out of injection tags and an actual value:

(define _applicable?
    (lambda (x)
        (and (pair? x)
             (case (car x)
                 ((subr fsubr lambda-abstraction)
                    (and (= 3 (length x))
                         (number? (cadr x))
                         (procedure? (caddr x))))
                 ((delta-abstraction gamma-abstraction)
                    (procedure? (cdr x)))
                 ((environment continuation)
                    (procedure? (cdr x)))
                 (else
                    #f)))))


; ----- the values in the initial environment ---------------------------------

; Evaluating a value designated by quote dereferences it:
(define _quote
    (lambda (l r k tau)
        (k (car l) tau)))


; As in Scheme, booleans are #t and #f, and in addition,
; the empty list stands for false, and anything that is not false is true:
(define _if
    (lambda (l r k tau)
        (_eval (car l) r (lambda (a tau)
                             (case a
                                 ((#t)
                                     (_eval (cadr l) r k tau))
                                 ((#f)
                                     (_eval (caddr l) r k tau))
                                 (else
                                     (if (null? a)
                                         (_eval (caddr l) r k tau)
                                         (_eval (cadr l) r k tau))))) tau)))


; lambda, delta, and gamma-abstractions evaluate to functions and reifiers:
(define _lambda
    (lambda (l r k tau)
        (k (_inLambda-Abstraction (length (car l))
                                  (lambda (lv k tau)
                                      (_eval (cadr l)
                                             (_extend_env (car l) lv r)
                                             k
                                             tau)))
           tau)))

(define _inLambda-Abstraction
    (lambda (n a)
        (list 'lambda-abstraction n a)))


(define _delta
    (lambda (l r k tau)
        (if (not (= (length (car l)) 3))
            (_wrong '_delta "list of formal parameters" (car l))
            (k (_inDelta-Abstraction (lambda (ee rr kk rho kappa tau)
                                         (_eval (cadr l)
                                                (_extend_env (car l)
                                                         (list ee rr kk)
                                                         rho)
                                                kappa
                                                tau)))
               tau))))

(define _inDelta-Abstraction
    (lambda (a)
        (cons 'delta-abstraction a)))


(define _gamma
    (lambda (l r k stau)
        (if (not (= (length (car l)) 3))
            (_wrong '_gamma "list of formal parameters" (car l))
            (k (_inGamma-Abstraction (lambda (ee rr kk kappa tau)
                                          (_eval (cadr l)
                                                 (_extend_env (car l)
                                                          (list ee rr kk)
                                                          (_top-env stau))
                                                 kappa
                                                 tau)))
               stau))))

(define _inGamma-Abstraction
    (lambda (a)
        (cons 'gamma-abstraction a)))



; A common definition affects the common environment:
(define _common-define
    (lambda (l r k tau)
        (if (not (_identifier? (car l)))
            (_wrong '_common-define "undefinable" (car l))
            (_eval
                (cadr l)
                r
                (lambda (a tau)
                    (let ((pos (_index (car l) table-common-identifiers)))
                        (if (isNatural? pos)
                            (begin
                                (_update (_nth pos table-common-values) a)
                                (k (car l) tau))
                            (begin
                                (set! table-common-identifiers
                                      (cons (car l) table-common-identifiers))
                                (set! table-common-values
                                      (cons a table-common-values))
                                (k (car l) tau))))) tau))))



; A definition affects the global environment of the current level.
(define _define
    (lambda (l r k tau)
        (if (not (_identifier? (car l)))
            (_wrong '_define "undefinable" (car l))
            (_eval
                (cadr l)
                r
                (lambda (a tau)
                    (let* ((global-env (car (last-pair r)))
                           (pos (_index (car l) (car global-env))))
                        (if (isNatural? pos)
                            (begin
                                (_update (_nth pos (cdr global-env)) a)
                                (k (car l) tau))
                            (begin
                                (set-car! global-env
                                          (cons (car l) (car global-env)))
                                (set-cdr! global-env
                                      (cons a (cdr global-env)))
                                (k (car l) tau))))) tau))))



; An assignment affects the representation of the environment. Assigning
; a common identifier shadows it at the current level.
(define _set!
    (lambda (l r k tau)
        (if (not (_identifier? (car l)))
            (_wrong '_set! "undefinable" (car l))
            (_eval (cadr l) r (lambda (a tau)
                                  (_L_set! (car l) a r k tau)) tau))))

(define _L_set!
    (lambda (i v r k tau)
        (let ((pos (_index i (caar r))))
            (if (isNatural? pos)
                (let* ((location (_nth pos (cdar r)))
                       (previous-value (_access location)))
                    (begin
                        (_update location v)
                        (k previous-value tau)))
                (if (null? (cdr r))
                    (let ((pos (_index i table-common-identifiers)))
                        (if (isNatural? pos)
                            (begin
                                (set-car! (car r) (cons i (caar r)))
                                (set-cdr! (car r) (cons v (cdar r)))
                                (k (_access (_nth pos table-common-values))
                                   tau))
                            (_wrong '_L_set! "undefined variable" i)))
                    (_L_set! i v (cdr r) k tau))))))



; The extensional if, that evaluates all its arguments:
(define _ef
    (lambda (p at af)
        (case p
            ((#t)
                at)
            ((#f)
                af)
            (else
                (if (null? p) af at)))))


; The case statement:
(define _case 
    (lambda (l r k tau)
        (_eval (car l) r (lambda (a tau)
                                (_case_loop a (cdr l) r k tau)) tau)))

(define _case_loop
    (lambda (a l r k tau)
        (if (null? l)
            (_wrong '_case_loop "unmatched" a)
            (if (equal? (caar l) 'else)
                (_eval (cadr (car l)) r k tau)
                (if ((if (pair? (caar l)) member equal?) a (caar l))
                    (_eval (cadr (car l)) r k tau)
                    (_case_loop a (cdr l) r k tau))))))


; The conjunctive expression:
(define _and
    (lambda (l r k tau)
        (if (null? l)
            (k #t tau)
            (_and_loop l r k tau))))

(define _and_loop
    (lambda (l r k tau)
        (if (null? (cdr l))
            (_eval (car l) r k tau)
            (_eval (car l) r (lambda (a tau)
                                 (if (or (null? a) (equal? a #f))
                                     (k #f tau)
                                     (_and_loop (cdr l) r k tau))) tau))))


; The disjunctive expression:
(define _or
    (lambda (l r k tau)
        (if (null? l)
            (k #f tau)
            (_or_loop l r k tau))))

(define _or_loop
    (lambda (l r k tau)
        (if (null? (cdr l))
            (_eval (car l) r k tau)
            (_eval (car l) r (lambda (a tau)
                                 (if (or (null? a) (equal? a #f))
                                     (_or_loop (cdr l) r k tau)
                                     (k a tau))) tau))))


; The sequence statement:
(define _begin
    (lambda (l r k tau)
        (if (null? (cdr l))
            (_eval (car l) r k tau)
            (_eval (car l) r (lambda (a tau)
                                (_begin (cdr l) r k tau)) tau))))


; Reading is done either from the implicit input stream
; or from an explicit port:
(define _read
    (lambda (l r k tau)
        (if (null? l)
            (k (read) tau)
            (if (null? (cdr l))
                (_eval (car l)
                       r
                       (lambda (port tau)
                           (k (read port) tau))
                       tau)
                (_wrong '_read "arity mismatch" l)))))


; Loading a file redirects the input stream:
(define _load
    (lambda (l r k tau)
        (_eval (car l)
               r
               (lambda (file tau)
                   (_load_loop file (open-input-file file) r k tau))
               tau)))

(define _load_loop
    (lambda (file port r k tau)
        (let ((it (read port)))
            (if (eof-object? it)
                (begin
                    (newline)
                    (close-input-port port)
                    (k file tau))
                (let ((a (_eval it r (lambda (a tau) (list 'okay a tau)) tau)))
                    (if (equal? (car a) 'okay)
                        (begin
                            (display (cadr a)) (display " ") (flush-output)
                            (_load_loop file port r k tau))
                        (begin
                            (close-input-port port)
                            a)))))))


; A file can be loaded without displaying the results of the evaluations:
(define _mute-load
    (lambda (l r k tau)
        (_eval (car l)
               r
               (lambda (file tau)
                   (_mute-load_loop file (open-input-file file) r k tau))
               tau)))

(define _mute-load_loop
    (lambda (file port r k tau)
        (let ((it (read port)))
            (if (eof-object? it)
                (begin
                    (close-input-port port)
                    (k file tau))
                (let ((a (_eval it r (lambda (a tau) (list 'okay a tau)) tau)))
                    (if (equal? (car a) 'okay)
                        (_mute-load_loop file port r k tau)
                        (begin
                            (close-input-port port)
                            a)))))))



; A new interactive level can be spawned:
(define _openloop
    (lambda (l r k tau)
        (case (length l)
            (1
                (_eval (car l)
                       r
                       (lambda (new-level tau)
                           ((_generate_toplevel-continuation
                                        new-level (make-initial-environment))
                                blond-banner
                                (_meta-push r k tau)))
                       tau))
            (2
                (_eval (car l)
                       r
                       (lambda (new-level tau)
                           (_eval (cadr l)
                                  r
                                  (lambda (new-env tau)
                                      (if (_environment? new-env)
                                          ((_generate_toplevel-continuation
                                                        new-level
                                                        (_env-down new-env))
                                                blond-banner
                                                (_meta-push r k tau))
                                          (_wrong '_openloop
                                                  "not a reified environment"
                                                  new-env)))
                                  tau))
                       tau))
            (else
                (_wrong '_openloop "wrong arity" l)))))


; Extending a reified environment needs reflecting it & reifying its extension:
(define _access
    car)

(define _update
    set-car!)


(define _extend-reified-environment
    (lambda (l r k tau)
        (_eval (car l)
               r
               (lambda (a1 tau)
                   (_eval (cadr l)
                          r
                          (lambda (a2 tau)
                              (_eval (caddr l)
                                     r
                                     (lambda (a3 tau)
                                         (_extend a1 a2 a3 k tau))
                                     tau))
                          tau))
               tau)))


(define _extend
    (lambda (li lv r k tau)
        (cond
            ((not (pair? li))
                (_wrong '_extend-reified-environment
                        "not a list of identifiers"
                        li))
            ((not (pair? lv))        
                (_wrong '_extend-reified-environment
                        "not a list of values"
                        li))
            ((not (= (length li) (length lv)))
                (_wrong '_extend-reified-environment
                        "lists mismatch"
                        (list li lv)))
            ((not (_environment? r))
                (_wrong '_extend-reified-environment
                        "not a reified environment"
                        r))
            (else
                (k (_env-up (_extend_env li lv (_env-down r))) tau)))))



; The following describes the usual block structures let and letrec.
; A recursive binding is achieved by side-effect rather than by a fixed point.
(define _let                    ; assumes a well-formed let construction
    (lambda (l r k tau)
        (if (null? (car l))
            (_eval (cadr l) r k tau)
            (_let_evlis (car l)
                        r
                        (lambda (lv tau)
                            (_eval (cadr l)
                                   (_extend_env (_let_idlis (car l)) lv r)
                                   k
                                   tau))
                        tau))))

(define _let_evlis
    (lambda (h r k tau)
        (_eval (cadr (car h))
               r
               (lambda (v tau)
                   (if (null? (cdr h))
                           (k (list v) tau)
                           (_let_evlis (cdr h)
                                       r
                                       (lambda (lv tau)
                                           (k (cons v lv) tau))
                                       tau)))
               tau)))

(define _let_idlis
    (lambda (h)         ; (map car h)
        (if (null? h)
            '()
            (cons (caar h) (_let_idlis (cdr h))))))


(define _letrec                 ; assumes a well-formed letrec construction
    (lambda (l r k tau)
        (if (null? (car l))
            (_eval (cadr l) r k tau)
            (let ((r (_extend_env (_let_idlis (car l)) '() r)))
                (_let_evlis (car l)
                            r
                            (lambda (lv tau)
                                (begin
                                    (set-cdr! (car r) lv)
                                    (_eval (cadr l) r k tau)))
                            tau)))))


(define _rec                    ; assumes a well-formed rec construction
    (lambda (l r k tau)
        (let ((r (_extend_env (list (car l)) '() r)))
            (_eval (cadr l) r (lambda (a tau)
                                  (begin
                                      (set-cdr! (car r) (list a))
                                      (k a tau))) tau))))


(define _let*                   ; assumes a well-formed let* construction
    (lambda (l r k tau)
        (_let*_evlis (car l) (cadr l) r k tau)))

(define _let*_evlis
    (lambda (h b r k tau)
        (if (null? h)
            (_eval b r k tau)
            (_eval (cadr (car h))
                   r
                   (lambda (a tau)
                       (_let*_evlis (cdr h)
                                    b
                                    (_extend_env (list (caar h)) (list a) r)
                                    k
                                    tau))
                   tau))))



; Blond provides the usual conditional cond:
(define _cond
    (lambda (l r k tau)
        (if (null? l)
            (k "unmatched-cond" tau)
            (if (equal? (caar l) 'else)
                (_eval (cadr (car l)) r k tau)
                (_eval (caar l)
                       r
                       (lambda (a tau)
                           (if (or (equal? a #f) (null? a))
                               (_cond (cdr l) r k tau)
                               (_eval (cadr (car l)) r k tau)))
                       tau)))))



; Both a reified instance of the initial environment and a reified
; instance of a bottom level loop continuation are available:
(define _reify-new-environment
    (lambda ()
        (_env-up (make-initial-environment))))


(define _reify-new-continuation
    (lambda (l r k tau)
        (case (length l)
            (1
                (_eval (car l)
                       r
                       (lambda (level tau)
                           (k (_cont-up (_generate_toplevel-continuation
                                            level
                                            (make-initial-environment))) tau))
                       tau))
            (2
                (_eval (car l)
                       r
                       (lambda (level tau)
                           (_eval (cadr l)
                                  r
                                  (lambda (env tau)
                                      (if (_environment? env)
                                          (k (_cont-up
                                             (_generate_toplevel-continuation
                                                 level (_env-down env)))
                                             tau)
                                          (_wrong '_reify-new-continuation
                                                  "not a reified environment"
                                                  env)))
                                  tau))
                       tau))
            (else
                (_wrong '_reify-new-continuation "arity mismatch" l)))))


; Continuations can be applied in a pushy or in a jumpy mode:
(define _continuation-mode
    (lambda ()
        (if (eq? _apply_continuation _apply_continuation-jumpy)
            'jumpy
            'pushy)))


(define _switch-continuation-mode
    (lambda ()
        (if (eq? _apply_continuation _apply_continuation-jumpy)
            (begin
                (set! _apply_continuation _apply_continuation-pushy)
                'pushy)
            (begin
                (set! _apply_continuation _apply_continuation-jumpy)
                'jumpy))))


; Ending a session ignores the current continuation and meta-continuation:
(define _blond-exit
    (lambda (l r k tau)
        "farvel!"))



; ----- the initial environment -----------------------------------------------

(define table-common-identifiers
      '(nil
        car cdr
        caar cadr
        cdar cddr
        caddr cdddr
        last-pair
        null? atom? pair?
        number? string? symbol?
        zero? add1 sub1
        + - *
        cons equal?
        = boolean?
        negative? positive?
        procedure?
        quote
        lambda
        delta meaning gamma
        if ef
        common-define define
        set!
        case
        and or
        list
        set-car! set-cdr!
        begin
        display print
        pretty-print newline
        not length
        load mute-load read
        open-input-file eof-object?
        close-input-port
        flush-output
        openloop
        extend-reified-environment
        let letrec
        rec let*
        cond
        blond-exit
        reify-new-environment
        reify-new-continuation
        continuation-mode
        switch-continuation-mode
        ))

(define _inSubr
    (lambda (arity function-value)
        (list 'subr arity function-value)))

(define _inFsubr
    (lambda (arity function-value)
        (list 'fsubr arity function-value)))


(define table-common-values
  (list ()
        (_inSubr 1 car) (_inSubr 1 cdr)
        (_inSubr 1 caar) (_inSubr 1 cadr)
        (_inSubr 1 cdar) (_inSubr 1 cddr)
        (_inSubr 1 caddr) (_inSubr 1 cdddr)
        (_inSubr 1 last-pair)
        (_inSubr 1 null?) (_inSubr 1 atom?) (_inSubr 1 pair?)
        (_inSubr 1 number?) (_inSubr 1 string?) (_inSubr 1 symbol?)
        (_inSubr 1 zero?) (_inSubr 1 add1) (_inSubr 1 sub1)
        (_inSubr 2 +) (_inSubr 2 -) (_inSubr 2 *)
        (_inSubr 2 cons) (_inSubr 2 equal?)
        (_inSubr 2 =) (_inSubr 1 boolean?)
        (_inSubr 1 negative?) (_inSubr 1 positive?)
        (_inSubr 1 _applicable?)
        (_inFsubr 1 _quote)
        (_inFsubr 2 _lambda)
        (_inFsubr 2 _delta) (_inFsubr 3 _meaning) (_inFsubr 2 _gamma)
        (_inFsubr 3 _if) (_inSubr 3 _ef)
        (_inFsubr 2 _common-define) (_inFsubr 2 _define)
        (_inFsubr 2 _set!)
        (_inFsubr 0 _case)
        (_inFsubr 0 _and) (_inFsubr 0 _or)
        (_inFsubr 0 _evlis)
        (_inSubr 2 set-car!) (_inSubr 2 set-cdr!)
        (_inFsubr 0 _begin)
        (_inSubr 1 display) (_inSubr 1 pretty-print)
        (_inSubr 1 pretty-print) (_inSubr 0 newline)
        (_inSubr 1 not) (_inSubr 1 length)
        (_inFsubr 1 _load) (_inFsubr 1 _mute-load) (_inFsubr 0 _read)
        (_inSubr 1 open-input-file) (_inSubr 1 eof-object?)
        (_inSubr 1 close-input-port)
        (_inSubr 0 flush-output)
        (_inFsubr 0 _openloop)
        (_inFsubr 3 _extend-reified-environment)
        (_inFsubr 2 _let) (_inFsubr 2 _letrec)
        (_inFsubr 2 _rec) (_inFsubr 2 _let*)
        (_inFsubr 0 _cond)
        (_inFsubr 0 _blond-exit)
        (_inSubr 0 _reify-new-environment)
        (_inFsubr 0 _reify-new-continuation)
        (_inSubr 0 _continuation-mode)
        (_inSubr 0 _switch-continuation-mode)
        ))



; Miscalleneous:
(define _wrong
    list)

(define _constant?
    (lambda (x)
        (or (null? x)
            (number? x)
            (string? x)
            (boolean? x))))

(define _identifier?
    symbol?)

(define _index
    (lambda (i l)
        (_index_loop i 0 l)))

(define _index_loop
    (lambda (i n l)
        (if (null? l)
            -1
            (if (equal? i (car l))
                n
                (_index_loop i (add1 n) (cdr l))))))

(define isNatural?
    (lambda (n)
	(>= n 0)))

(define _nth
    (lambda (n l)
        (list-tail l n)))

(define _fetch-ftype car)
(define _fetch-arity cadr)
(define _fetch-value caddr)

; Basic lexical environment extension:
(define _extend_env
    (lambda (par l env)
        (cons (cons par l) env)))



; ----- how Blond hangs together ----------------------------------------------

; The starting point:
(define blond
    (lambda ()
        ((_generate_toplevel-continuation initial-level
                                          (make-initial-environment))
             blond-banner (initial-meta-continuation initial-level))))

; The initial level and how to manifest a level above it:
(define initial-level 0)
(define level-above add1)

; The generation of an empty global environment:
(define make-initial-environment
    (lambda ()
        (_extend_env () () ())))


; Some fantasy:
(define blond-banner		; cf. Full Metal Jacket, Stanley Kubrick (1987)
    "Is it John McCarthy or is it me?")
(define blond-banner		; cf. Brazil, Terry Gyndham (1985)
    "It's okay, I don't like you either.")
(define blond-banner		; "til tjeneste" means "at your service"
    "til tjeneste")		; it is an old-fashioned formula in Danish
(define blond-banner
    "started up")
(define blond-banner		; cf. 3-Lisp
    "[Thud.]")
(define blond-banner
    "toplevel")
(define blond-banner
    "blond")
(define blond-banner
    "-*-")
(define blond-banner
    "Blond is winning again")
(define blond-banner		; a la Brown
    "starting-up")
(define blond-banner
    "bottom-level")


; A self-generating initial meta-continuation:
(define initial-meta-continuation
    (lambda (level)
        (let ((an-initial-environment (make-initial-environment)))
            (lambda (selector)
                (case selector
                    (env
                        an-initial-environment)
                    (cont
                        (_generate_toplevel-continuation
                            (level-above level)
                            an-initial-environment))
                    (meta-continuation
                        (initial-meta-continuation (level-above level)))
                    (else
                        (_error foobarbaz)))))))


; How to get the top-most environment:
(define _top-env
    (lambda (meta-continuation)
        (meta-continuation 'env)))

; How to get the top-most continuation:
(define _top-cont
    (lambda (meta-continuation)
        (meta-continuation 'cont)))

; How to get the next meta-continuation:
(define _meta-pop
    (lambda (meta-continuation)
        (meta-continuation 'meta-continuation)))

; How to get a new meta-continuation:
(define _meta-push
    (lambda (r k tau)
        (lambda (selector)
            (case selector
                (env r)
                (cont k)
                (meta-continuation tau)
                (else (_error foobarbaz))))))


; Generation of a new top-level loop:
(define _generate_toplevel-continuation
    (lambda (my-level my-environment)
        (letrec ((elementary-loop
                    (lambda (iteration)
                        (lambda (val meta-continuation)
                            (begin
                                (_print my-level iteration val)
                                (_eval (read)
                                       my-environment
                                       (elementary-loop
                                            (next-iteration iteration))
                                       meta-continuation))))))
            (elementary-loop first-iteration))))

; The first iteration and how to manifest the following ones:
(define first-iteration 0)
(define next-iteration add1)



; A display mechanism for the prompts:
(define _print
    (lambda (l i v)
        (begin
            (display l)
            (display "-")
            (display i)
            (display ": ")
            (pretty-print v)
;           (newline)           ; in the case it was just (display v)
            (display l)
            (display "-")
            (display (next-iteration i))
            (display "> ")
            (flush-output))))

; ----- end of the file -------------------------------------------------------


