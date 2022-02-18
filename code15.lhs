This is a literate haskell file, tested in GHC 7.8.2. to GHC 8.10.4.
If you are running an earlier version that does not support EmptyCase,
you can remove it from the language extensions required below and
replace the definition of abort below to "cheat" by using an
infinite loop to produce any result type: abort x = abort x

> {-# LANGUAGE EmptyDataDecls, EmptyCase, RankNTypes, ScopedTypeVariables #-}

Curry-Howard Isomorphism: Proposition as Types

- Implication corresponds to function abstraction, and its elimination (modus ponens) to application.
- Conjunction corresponds to the pair type (cartesian product).
- Disjunction corresponds to a disjoint sum (think tagged list in Scheme).
- Each algebraic datatype is a disjoint sum of products.

Further reading:
- Lecture notes by Frank Pfenning on Constructive Logic
  http://www.cs.cmu.edu/~fp/courses/15317-f09/schedule.html
  - Natural Deduction:  http://www.cs.cmu.edu/~fp/courses/15317-f09/lectures/02-natded.pdf
  - Proofs as Programs: http://www.cs.cmu.edu/~fp/courses/15317-f09/lectures/04-pap.pdf
- Church's Thesis and Functional Programming by David A. Turner
  http://www.cs.kent.ac.uk/people/staff/dat/miranda/ctfp.pdf
- Total Functional Programming by David A. Turner
  http://www.jucs.org/jucs_10_7/total_functional_programming
- Propositions as Types by Phil Wadler
  http://homepages.inf.ed.ac.uk/wadler/papers/propositions-as-types/propositions-as-types.pdf
- Theorems for Free by Phil Wadler
  http://ttic.uchicago.edu/~dreyer/course/papers/wadler.pdf

conjunction: A /\ B

  A true, B true
----------------------- I/\
  A /\ B true

  A /\ B true
----------------------- E/\1
  A true

  A /\ B true
----------------------- E/\2
  B true

proposition as types for conjunction: (A /\ B) ~~ (A, B) or (A x B) cartesian product

  Ma: A, Mb: B
----------------------- I/\
  (Ma, Mb): (A, B)

  M: (A, B)
----------------------- E/\1
  fst M: A

  M: (A, B)
----------------------- E/\2
  snd M: B

implication: A -> B

  A true
  ------ u
    .
    .
    .
  B true
----------------------- I->u
  A -> B true


  A true, A -> B true
----------------------- E->
  B true

proposition as types for implication: -> (implication) ~~ -> (function:abstraction/application)

  u: A
  ------ u
    .
    .
    .
  M: B
----------------------- I->u
  (\u:A -> M): A -> B


  M2: A, M1: A -> B
----------------------- E->
  (M1 M2)


disjunction: A \/ B

  A true
----------------------- I\/1
  A \/ B true

  B true
----------------------- I\/2
  A \/ B true

              
             A        B
          ------ u ------w
             .        .
             .        .
             .        .
A\/B true    C        C
-------------------------- E\/u,w
   C true

proposition as types for disjunction: (A \/ B) ~~ (A | B) or (A + B) disjoint sum

  M: A
----------------------- I\/1
  inl M: A+B

  M: B
----------------------- I\/2
  inr M: A+B

              
            u:A      w:B
          ------ u ------w
             .        .
             .        .
             .        .
M:A+B      Mu:C     Mw:C
------------------------------- E\/u,w
case M of u -> Mu | w -> Mw : C

> import Data.Either

true: empty product

> data T = T

false: empty sum

> data F

"ex falso quodlibet": false implies anything!

> abort :: F -> a
> abort x = case x of {}

> idF :: F -> F
> idF x = x

negation

> type Not a = a -> F

algebraic datatypes

> data And a b = AndBoth a b
> data Or a b = OrLeft a | OrRight b
> data Nat = Z | S Nat
> data List a = Nil | Cons a (List a)

classical logic

> type ProofByContradiction a = (Not a -> F) -> a
> type DoubleNegationElim a = (Not (Not a)) -> a
> type ExcludedMiddle a = Either a (Not a)
> type PierceLaw a b = ((a->b)->a)->a

> type ProofByContradiction4All = forall a. ProofByContradiction a
> type DoubleNegationElim4All = forall a. DoubleNegationElim a
> type ExcludedMiddle4All = forall a. ExcludedMiddle a
> type PierceLaw4All = forall a b. PierceLaw a b

exercises

1. Show that A /\ B -> B /\ A.
2. Show that A /\ B -> A \/ B.
3. Show that (B \/ C) -> (B -> C) -> C.
4. Show that (B -> C) -> (A -> B) -> (A -> C). What program does this type/proposition correspond to?
5. (Hard) Classical logic: show that any of the above axioms for classical logic are equivalent.

solutions to exercises

exercise 1

> ex1 :: (a, b) -> (b, a)
> ex1 = \ab -> (snd ab, fst ab)

exercise 2

> ex2 :: (a, b) -> Either a b
> ex2 = \ab -> Left (fst ab)

> ex2alt :: (a, b) -> Either a b
> ex2alt = \ab -> Right (snd ab)

exercise 3

> ex3 :: Either b c -> (b -> c) -> c
> ex3 = \boc -> \fbc -> case boc of
>   Left b -> fbc b
>   Right c -> c

exericse 4 (function composition)

> ex4 :: (b -> c) -> (a -> b) -> (a -> c)
> ex4 = \g -> \f -> \x -> g (f x)

exercise 5

> classical12 :: ProofByContradiction4All -> DoubleNegationElim4All
> classical12 = \(h::ProofByContradiction4All) -> h

> classical23 :: DoubleNegationElim4All -> ExcludedMiddle4All
> classical23 =
>   \(h::DoubleNegationElim4All) ->
>   h (\(g::Not (ExcludedMiddle a)) -> g (Left (h (\(i::Not a) -> g (Right i)))))

> useEM :: ExcludedMiddle4All -> ExcludedMiddle a
> useEM h = h

> classical34 :: ExcludedMiddle4All -> PierceLaw4All
> classical34 =
>   \(h::ExcludedMiddle4All) -> \f -> case (useEM h) of
>     Left  a -> a
>     Right n -> f (\a -> abort (n a))

> classical41 :: PierceLaw4All -> ProofByContradiction4All
> classical41 =
>   \(h::PierceLaw4All) -> \(f::(a->F)->F) -> h (\g -> abort (f g))
