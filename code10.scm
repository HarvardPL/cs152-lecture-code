;; excerpt from https://github.com/namin/lambdajam/blob/master/script.scm
;; see also https://github.com/namin/lambdajam/blob/master/NOTES.md#cps-continuation-passing-style
;; see also https://github.com/namin/lambdajam/blob/master/NOTES.md#trampolining

;;; Program Transformations

;;; CPS: continuation-passing style

;;; continuations
;;; representation of the rest of the work to be done

(+ 1 2 (+ 3 4))
((lambda (v) v) (+ 1 2 (+ 3 4)))
((lambda (HOLE) (+ 1 2 HOLE)) (+ 3 4)) ;; 12
((lambda (v) (+ 1 v (+ 3 4))) 2)

(+ (+ 1 2) (+ 3 4))
((lambda (v) (+ v (+ 3 4))) (+ 1 2))
((lambda (v) (+ (+ 1 2) v)) (+ 3 4))

(lambda (v) v) ;; identity continuation

;;; Continuation-Passing Style

;;; Gateway drug of program transformations:
;;; Since it ensures a program has useful properties, such as:
;;; - all serious calls being in tail position,
;;; - all arguments to calls are simple,
;;; - fix order of evaluation.

;;; direct-style
(define factorial
  (lambda (n)
    (if (= n 0)
        1
        (* n (factorial (- n 1))))))
(trace factorial)
;;(factorial -1)

;;; accumulator
(define factorial-iter
  (lambda (n acc)
    (if (= n 0)
        acc
        (factorial-iter (- n 1) (* acc n)))))
(define factorial
  (lambda (n)
    (factorial-iter n 1)))
(trace factorial-iter)
;;(factorial -1)

;;; Steps
;;; - Change the name with -cps.
;;; - Add k argument to lambda.
;;; - Return by applying k.
;;; - Serious calls need to be transformed.

(define factorial-cps
  (lambda (n k)
    (if (= n 0)
        (k 1)
        (factorial-cps (- n 1) (lambda (v)
                                 (k (* n v)))))))
(define factorial
  (lambda (n)
    (factorial-cps n (lambda (v) v))))
(trace factorial-cps)
(factorial 5)

;;; CPSing is a mechanical transformation,
;;; which can be applied multiple times
(define factorial-cps2
  (lambda (n k1 k)
    (if (<= n 0)
        (k1 1 k)
        (factorial-cps2 (- n 1) (lambda (r k) (k1 (* n r) k)) k))))
(define factorial
  (lambda (n)
    (factorial-cps2 n (lambda (v k) (k v)) (lambda (v) v))))
(trace factorial-cps2)
(factorial 5)

;;; direct-style
(define fib
  (lambda (n)
    (if (< n 2) n
        (+ (fib (- n 1)) (fib (- n 2))))))

(define fib-cps
  (lambda (n k)
    (if (< n 2) (k n)
        (fib-cps (- n 2)
                 (lambda (v2)
                   (fib-cps (- n 1) (lambda (v1)
                                      (k (+ v1 v2)))))))))
(define fib
  (lambda (n)
    (fib-cps n (lambda (v) v))))
(fib 5)

;;; Trampolining

;;; We cannot trampoline without CPSing first,
;;; because the non-tail calls must return the expected type, not a procedure.
;;; For example, with Fibonacci, the + call would get confused getting procedures (thunks).

;;; When compiling to C, CPS by itself does not guarantee a bounded stack.
;;; Trampolining is one solution.

;;; Just wrap a thunk around the body of the CPSed function.
;;; Now, the driver needs to keep applying the returned thunk until it's not a procedure anymore.

(define factorial-cps
  (lambda (n k)
    (lambda ()
      (if (= n 0)
          (k 1)
          (factorial-cps (- n 1) (lambda (v)
                                   (k (* n v))))))))

;;; Instead of grossly thunking the whole body, we can be more fine-grained about it.
;;; Only need to thunk parts that consume unbounded stack.

(define factorial-cps
  (lambda (n k)
    (if (= n 0)
        (lambda () (k 1))
        (lambda () (factorial-cps (- n 1) (lambda (v)
                                       (k (* n v))))))))
(define factorial
  (lambda (n)
    (let ((r (factorial-cps n (lambda (v) v))))
      (while (procedure? r)
             (set! r (r)) ;; body of the while
             r)) ;; return after the while
    ))

(define factorial
  (lambda (n)
    (let loop ((r (factorial-cps n (lambda (v) v))))
      (if (procedure? r)
          (loop (r))
          r))))


