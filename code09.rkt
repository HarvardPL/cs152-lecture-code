#lang racket
(require redex)
(provide λ λcbv λcbn cbv cbn)

(define-language λ
  (e x
     (λ (x) e)
     (e e))
  (v (λ (x) e))
  (x variable-not-otherwise-mentioned))

(define-extended-language λcbv λ
  (E hole
     (E e)
     (v E)))

(define-extended-language λcbn λ
  (E hole
     (E e)))

(define cbv
  (reduction-relation
   λcbv
   (--> (in-hole E ((λ (x) e) v))
        (in-hole E (subst x v e))
        "β")))

(define cbn
  (reduction-relation
   λcbn
   (--> (in-hole E ((λ (x) e) e_2))
        (in-hole E (subst x v e_2))
        "β")))

(define-metafunction λ
  subst : x any any -> any
  ;; 1. x_1 bound, so don't continue in λ body
  [(subst x_1 any_1 (λ (x_1) any_2))
   (λ (x_1) any_2)]
  ;; 2. general purpose capture avoiding case
  [(subst x_1 any_1 (λ (x_2) any_2))
   (λ (x_new)
     (subst x_1 any_1
            (subst-var x_2 x_new
                       any_2)))
   (where (x_new)
          ,(variables-not-in
            (term (x_1 any_1 any_2)) 
            (term (x_2))))]
  ;; 3. replace x_1 with e_1
  [(subst x_1 any_1 x_1) any_1]
  ;; 4. x_1 and x_2 are different, so don't replace
  [(subst x_1 any_1 x_2) x_2]
  ;; the last cases cover all other expressions
  [(subst x_1 any_1 (any_2 ...))
   ((subst x_1 any_1 any_2) ...)]
  [(subst x_1 any_1 any_2) any_2])

(define-metafunction λ
  subst-var : x any any -> any
  [(subst-var x_1 any_1 x_1) any_1]
  [(subst-var x_1 any_1 (any_2 ...))
   ((subst-var x_1 any_1 any_2) ...)]
  [(subst-var x_1 any_1 any_2) any_2])

'subst
(term (subst x (λ (x) x) (x (λ (x) x))))
'cbv
(apply-reduction-relation cbv (term ((λ (x) x) (λ (x) x))))
(apply-reduction-relation cbv (term ((λ (t) (λ (f) t)) ((λ (x) x) (λ (x) x)))))
'cbn
(apply-reduction-relation cbn (term ((λ (x) x) (λ (x) x))))
(apply-reduction-relation cbn (term ((λ (t) (λ (f) t)) ((λ (x) x) (λ (x) x)))))