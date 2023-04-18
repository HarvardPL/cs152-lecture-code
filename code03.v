From Coq Require Import ZArith.ZArith.
From Coq Require Import Strings.String.
Open Scope string_scope.
Require Import Coq.Program.Equality. (* for dependent induction *)

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
  eapply multi_step. eauto using sstep.
  eapply multi_step. eauto using sstep.
  eapply multi_step. eauto using sstep.
  eapply multi_step. eauto using sstep.
  eapply multi_step. eauto using sstep.
  eapply multi_refl.
Qed.

Theorem progress :
  forall e s,
    (exists n, EInt n = e) \/
    (exists e' s', (e, s) --> (e', s')).
Proof.
  intro e. induction e; intro s.
  - (* Var *)
    right.
    eexists. exists s.
    eapply SSVar.
  - (* Int *)
    left.
    exists i.
    reflexivity.
  - (* EAdd *)
    right.
    destruct (IHe1 s) as [IHval1 | IHstep1].
    + destruct IHval1 as [n1 IHval1].
      destruct (IHe2 s) as [IHval2 | IHstep2].
      * (* e1 value, e2, value *)
        destruct IHval2 as [n2 IHval2].
        subst.
        repeat eexists.
        eapply SSAdd.
      *  (* e1 value, e2 steps *)
        destruct IHstep2 as [e2' [s' IHstep2]].
        subst.
        repeat eexists.
        eapply SSRAdd. eapply IHstep2.
    + (* e1 steps *)
      destruct IHstep1 as [e1' [s' IHstep1]].
      repeat eexists.
      eapply SSLAdd. eapply IHstep1.
  - (* EMul *)
    right.
    destruct (IHe1 s) as [IHval1 | IHstep1].
    + destruct IHval1 as [n1 IHval1].
      destruct (IHe2 s) as [IHval2 | IHstep2].
      * (* e1 value, e2, value *)
        destruct IHval2 as [n2 IHval2].
        subst.
        repeat eexists.
        eapply SSMul.
      *  (* e1 value, e2 steps *)
        destruct IHstep2 as [e2' [s' IHstep2]].
        subst.
        repeat eexists.
        eapply SSRMul. eapply IHstep2.
    + (* e1 steps *)
      destruct IHstep1 as [e1' [s' IHstep1]].
      repeat eexists.
      eapply SSLMul. eapply IHstep1.
  - (* EAsg *)
    right.
    destruct (IHe1 s) as [IHval1 | IHstep1].
    + destruct IHval1 as [n1 IHval1].
      subst.
      repeat eexists.
      eapply SSAsg.
    + destruct IHstep1 as [e1' [s' IHstep1]].
      repeat eexists.
      eapply SSAsg1. eapply IHstep1.
Qed.
 
Theorem termination:
  forall e s0, exists s n, (e, s0) -->* (EInt n, s).
Admitted.

Theorem deterministic_result:
  forall e s0 s s' n n',
    (((e,s0) -->* (EInt n, s)) /\
     ((e,s0) -->* (EInt n', s')))
      ->
      (n = n' /\ s = s').
Admitted.

(*
For all expressions e and stores σ, if
< e,σ >−→< e′,σ′ > then
either σ = σ′ or
there is some variable x and integer n such that
σ′ = σ[x 􏰀→ n].
 *)
(* Coq as a proof checker rather a proof assistant.
Read out the paper proof from the script.
Use the interactive stepping to check your understanding. *)
Theorem incremental_update: forall e s e' s',
    (e,s) --> (e',s') ->
    (s = s') \/ exists x n, s' = StoreUpdate s x n.
Proof.
  intros. dependent induction H.
  - (* SSVar *)
    left. reflexivity.
  - (* SSAdd *)
    left. reflexivity.
  - (* SSMul *)
    left. reflexivity.
  - (* SSAsg *)
    right. repeat eexists.
  - (* SSLAdd *)
    destruct (IHsstep e1 s e1' s'); subst; try reflexivity.
    + (* same *) left. reflexivity.
    + (* update *) right. assumption.
  - (* SSRAdd *)
    destruct (IHsstep e2 s e2' s'); subst; try reflexivity.
    + (* same *) left. reflexivity.
    + (* update *) right. assumption.
  - (* SSLMul *)
    destruct (IHsstep e1 s e1' s'); subst; try reflexivity.
    + (* same *) left. reflexivity.
    + (* update *) right. assumption.
  - (* SSRMul *)
    destruct (IHsstep e2 s e2' s'); subst; try reflexivity.
    + (* same *) left. reflexivity.
    + (* update *) right. assumption.
  - (* SSAsg *)
    destruct (IHsstep e1 s e1' s'); subst; try reflexivity.
    + (* same *) left. reflexivity.
    + (* update *) right. assumption.
Qed.

(* Nada Amin's automation attempt,
there are four different sort of sub-cases.
Notice you lose the ability to step through.
*)
Theorem incremental_update_auto: forall e s e' s',
    (e,s) --> (e',s') ->
    (s = s') \/ exists x n, s' = StoreUpdate s x n.
Proof.
  intros.
  dependent induction H;
    try solve [left; reflexivity];
    try solve [right; repeat eexists];
    try solve [destruct (IHsstep e1 s e1' s'); subst; try reflexivity;
               try solve [left; reflexivity];
               try solve [right; assumption]];
    try solve [destruct (IHsstep e2 s e2' s'); subst; try reflexivity;
               try solve [left; reflexivity];
               try solve [right; assumption]].
Qed.

(* spelling out dependent induction... *)
Theorem incremental_update_auto2: forall e s e' s',
    (e,s) --> (e',s') ->
    (s = s') \/ exists x n, s' = StoreUpdate s x n.
Proof.
  intros.
  remember (e, s) as c.
  remember (e', s') as c'.
  generalize dependent s'.
  generalize dependent e'.
  generalize dependent s.
  generalize dependent e.
  induction H; intros;
  inversion Heqc; inversion Heqc'; subst;
  try solve [left; reflexivity];
  try solve [right; repeat eexists];
  try solve [eapply IHsstep; try reflexivity].
Qed.

(* Courtesy of Garrett Tanzer, structural induction is easier. *)
Theorem incremental_update_auto_more: forall e s e' s',
    (e,s) --> (e',s') ->
    (s = s') \/ exists x n, s' = StoreUpdate s x n.
Proof.
  induction e; intros; inversion H; eauto.
Qed.
