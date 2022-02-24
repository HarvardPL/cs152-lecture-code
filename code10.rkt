#lang racket

(require racket/trace)

(define fact
  (lambda (n)
    (if (<= n 0)
        1
        (* n (fact (- n 1))))))

(trace fact)
(fact 6)

(define fact-iter
  (lambda (n a)
    (if (<= n 0)
        a
        (fact-iter (- n 1) (* n a)))))

(trace fact-iter)
(fact-iter 6 1)

(define fact-cps
  (lambda (n k)
    (if (<= n 0)
        (k 1)
        (fact-cps (- n 1) (lambda (r) (k (* n r)))))))

(trace fact-cps)
(fact-cps 6 (lambda (x) x))

(define fib
  (lambda (n)
    (if (<= n 1)
        1
        (+ (fib (- n 1)) (fib (- n 2))))))

(trace fib)
(fib 5)

(define fact-cps2
  (lambda (n k1 k)
    (if (<= n 0)
        (k1 1 k)
        (fact-cps2 (- n 1) (lambda (r k) (k1 (* n r) k)) k))))

(fact-cps2 6 (lambda (x k) (k x)) (lambda (x) x))

