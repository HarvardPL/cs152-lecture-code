From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Strings.String.
Open Scope string_scope.

Definition Var := string.
Definition Var_eq := String.eqb.
Definition Int := Z.
Definition Int_add := Z.add.
Definition Int_mul := Z.mul.

Inductive Exp : Type :=
| EVar : Var -> Exp
| EInt : Int -> Exp
| EAdd : Exp -> Exp -> Exp
| EMul : Exp -> Exp -> Exp
| EAsg : Var -> Exp -> Exp -> Exp.

Definition Store := Var -> Int.

Definition Config := (Exp * Store)%type.

Definition StoreUpdate (s : Store) (x : Var) (n : Int) : Store :=
  fun (y : Var) => if (Var_eq x y) then n else (s y).

Reserved Notation "c1 '-->' c2" (at level 40).

Inductive sstep : Config -> Config -> Prop :=
| SSVar : forall x s,
            (EVar x, s) --> (EInt (s x), s)
| SSAdd : forall n m s,
            (EAdd (EInt n) (EInt m), s) --> (EInt (Int_add n m), s)
| SSMul : forall n m s,
            (EMul (EInt n) (EInt m), s) --> (EInt (Int_mul n m), s)
| SSAsg : forall n x e s,
            (EAsg x (EInt n) e, s) --> (e, StoreUpdate s x n)
| SSLAdd : forall e1 e1' e2 s s',
             (e1, s) --> (e1', s')  ->
             (EAdd e1 e2, s) --> (EAdd e1' e2, s')
| SSRAdd : forall n e2 e2' s s',
             (e2, s) --> (e2', s')  ->
             (EAdd (EInt n) e2, s) --> (EAdd (EInt n) e2', s')
| SSLMul : forall e1 e1' e2 s s',
             (e1, s) --> (e1', s')  ->
             (EMul e1 e2, s) --> (EMul e1' e2, s')
| SSRMul : forall n e2 e2' s s',
             (e2, s) --> (e2', s')  ->
             (EMul (EInt n) e2, s) --> (EMul (EInt n) e2', s')
| SSAsg1 : forall x e1 e1' e2 s s',
             (e1, s) --> (e1', s')  ->
             (EAsg x e1 e2, s) --> (EAsg x e1' e2, s')
where "c1 '-->' c2" := (sstep c1 c2).

Definition sigma : Store :=
  fun x => if Var_eq x "foo" then Zpos 4
           else if Var_eq x "bar" then Zpos 3
           else Z0.

Example foobar1 :
  (EMul
    (EAdd (EVar "foo") (EInt (Zpos 2)))
    (EAdd (EVar "bar") (EInt (Zpos 1))),
   sigma)
     -->
  (EMul
    (EAdd (EInt (Zpos 4)) (EInt (Zpos 2)))
    (EAdd (EVar "bar") (EInt (Zpos 1))),
   sigma).
Proof.
  apply SSLMul.
  apply SSLAdd.
  apply SSVar.
Qed.

Definition relation (X : Type) := X -> X -> Prop.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Definition multisstep := (multi sstep).
Notation "t1 '-->*' t2" := (multisstep t1 t2) (at level 40).

Example foobarv:
  ((EMul
      (EAdd (EVar "foo") (EInt (Zpos 2)))
      (EAdd (EVar "bar") (EInt (Zpos 1))),
   sigma)
     -->*
  ((EInt (Zpos 24),
   sigma))).
Proof.
  (* one-liner:
     repeat (try eapply multi_refl; eapply multi_step; eauto using sstep).
  *)
  eapply multi_step. eauto using sstep.
  eapply multi_step. eauto using sstep.
  eapply multi_step. eauto using sstep.
  eapply multi_step. eauto using sstep.
  eapply multi_step. eauto using sstep.
  eapply multi_refl.
Qed.

Definition progress :=
  forall e s,
    (exists n, EInt n = e) \/
    (exists e' s', (e, s) --> (e', s')).

Definition termination :=
  forall e s0, exists s n, (e, s0) -->* (EInt n, s).

Definition deterministic_result :=
  forall e s0 s s' n n',
    (((e,s0) -->* (EInt n, s)) /\
     ((e,s0) -->* (EInt n', s')))
      ->
      (n = n' /\ s = s').
