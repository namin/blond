(blond)
(load "exit.bl")
(exit "good bye")
(exit "farewell!")
(blond-exit)

(blond)
(add1 (openloop "marvin"))
((delta (e r k) 41))

((lambda (x) (openloop "foo")) 0)
((delta (e r k) x))

(let ((x 1))
  ((delta (e r k)
     (openloop "fox" r))))
x

((delta (e r k)
   (meaning (car e) r k)) "hello world")

(let ((x "hello world"))
  ((delta (e r k)
     (meaning (car e) r k)) x))

(meaning 1 (reify-new-environment) (lambda (x) x))

(meaning 1 (reify-new-environment) add1)

(meaning 'foobarbaz (reify-new-environment) quote)

(blond-exit)

(blond)
(define map
  (lambda (f l)  ; (Val -> Val) * List(Val) -> List(Val)
    ((rec self (lambda (l)
                 (if (null? l)
                     '()
                     (cons (f (car l)) (self (cdr l)))))) l)))
(map (lambda (x) x) '(1 2 3))
(map add1 '(1 2 3))
(map quote '(1 2 3))
(map (delta (e r k) e) '(1 2 3))

(blond-exit)

(blond)
((delta (e r k) (common-define env r)))
env
(env 'x)
(let ((x 'foobar))
  ((delta (e r k)
     (common-define env-x r))))
env-x
(env-x 'x)
(meaning 'x env-x (lambda (x) x))
(env-x 'x)
(env-x 'x 'foobarbaz)
(env-x 'x)
(meaning '(set! x 'foo) env-x (lambda (x) x))
(env-x 'x)

(meaning '(define y x) env-x (lambda (x) x))
(env-x 'y)
(blond-exit)

(blond)
((reify-new-continuation "rock"
                         (extend-reified-environment '(foo)
                                                     '("bar")
                                                     (reify-new-environment)))
 "bottom")
foo

((reify-new-continuation "Multivac") "new-bottom-level")
((delta (e r k) "bye"))

(blond-exit)

(blond)
(load "scheme.bl")
(continuation-mode)
(add1 (call/cc (lambda (k) 3)))
(add1 (call/cc (lambda (k) (k 3))))
(add1 (call/cc (lambda (k) (sub1 (k 3)))))
(call/cc (lambda (k) (common-define cont-0-6 k)))
'dummy ; cont-0-6 is bound to the continuation of iteration 6 at level 0
(cont-0-6 "back to 0-6")
(exit "exit from level 0")
(cont-0-6 "back again to 0-6")
(exit "exit again from level 0")
(blond-exit)

(blond)
(mute-load "scheme.bl")
(switch-continuation-mode)
(add1 (call/cc (lambda (k) 3)))
(add1 (call/cc (lambda (k) (k 3))))
(add1 (call/cc (lambda (k) (sub1 (k 3)))))
(call/cc (lambda (k) (common-define cont-0-6 k)))
'dummy ; cont-0-6 is bound to the continuation of iteration 6 at level 0
(cont-0-6 "back to 0-6")
(exit "exit from level 0")
(cont-0-6 "back again to 0-6")
(exit "exit again from level 0")
(exit 3)
(exit 3)
(exit "at last!")
(blond-exit)

(blond)
(load "nexit.bl")
(nexit 256)
(nexit 64)
(nexit 8)
(nexit 0)


