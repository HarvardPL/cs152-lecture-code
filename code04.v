From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Program.Equality.
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

Definition relation (X : Type) := X -> X -> Prop.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Definition multisstep := (multi sstep).
Notation "t1 '-->*' t2" := (multisstep t1 t2) (at level 40).

(* new content *)

Lemma multi_split: forall {X: Type} (R: relation X) x y z,
    multi R x y -> multi R y z -> multi R x z.
Proof.
  intros. dependent induction H.
  - assumption.
  - specialize (IHmulti H1).
    eapply multi_step. apply H. apply IHmulti.
Qed.

Definition FinalConfig := (Int * Store)%type.

Inductive lstep : Config -> FinalConfig -> Prop :=
| LSInt : forall n s,
            lstep (EInt n, s) (n, s)
| LSVar : forall x s,
            lstep (EVar x, s) (s x, s)
| LSAdd : forall n m e1 e2 s s' s'',
            lstep (e1, s) (n, s') ->
            lstep (e2, s') (m, s'') ->
              lstep (EAdd e1 e2, s) (Int_add n m, s'')
| LSMul : forall n m e1 e2 s s' s'',
            lstep (e1, s) (n, s') ->
            lstep (e2, s') (m, s'') ->
              lstep (EMul e1 e2, s) (Int_mul n m, s'')
| LSAsg : forall n m x e1 e2 s s' s'',
             lstep (e1, s) (n, s') ->
             lstep (e2, StoreUpdate s' x n) (m, s'') ->
               lstep (EAsg x e1 e2, s) (m, s'').

Definition sigma := fun x => if Var_eq x "bar" then Zpos 7 else Z0.
Definition sigma' := StoreUpdate sigma "foo" (Zpos 3).

Example foobar :
  lstep
    (EAsg "foo" (EInt (Zpos 3)) (EMul (EVar "foo") (EVar "bar")), sigma)
    (Zpos 21, sigma').
Proof.
  eapply LSAsg.
  - eapply LSInt.
  - unfold sigma'.
    assert (21%Z = Int_mul 3%Z 7%Z) by auto.
    rewrite H. eapply LSMul.
    + eapply LSVar.
    + eapply LSVar.
Qed.

Lemma lemma1Asg:
  forall e s s' n,
    (e, s) -->* (EInt n, s')  ->
    forall x e2,
      (EAsg x e e2, s) -->* (e2, StoreUpdate s' x n).
Proof.
  intros. dependent induction H.
  - eapply multi_step. eapply SSAsg. eapply multi_refl.
  - destruct y as (e'',s'').
    specialize (IHmulti e'' s'' s' n).
    assert ((e'', s'') ~= (e'', s'')) as T1 by reflexivity.
    assert ((EInt n, s') ~= (EInt n, s')) as T2 by reflexivity.
    specialize (IHmulti T1 T2).
    specialize (IHmulti x e2).
    eapply multi_step. eapply SSAsg1. eapply H. assumption.
Qed.

Lemma lemma1 :
  forall e s s' n,
    (e, s) -->* (EInt n, s')  ->
      forall n1 e2,
      (EAdd e e2, s) -->* (EAdd (EInt n) e2, s') /\
      (EMul e e2, s) -->* (EMul (EInt n) e2, s') /\
      (EAdd (EInt n1) e, s) -->* (EAdd (EInt n1) (EInt n), s') /\
      (EMul (EInt n1) e, s) -->* (EMul (EInt n1) (EInt n), s').
Proof.
  intros. dependent induction H.
  - repeat split; apply multi_refl.
  - destruct y as (e'',s'').
    specialize (IHmulti e'' s'' s' n).
    assert ((e'', s'') ~= (e'', s'')) as T1 by reflexivity.
    assert ((EInt n, s') ~= (EInt n, s')) as T2 by reflexivity.
    specialize (IHmulti T1 T2).
    specialize (IHmulti n1 e2).
    destruct IHmulti as [HLA [HLM [HRA HRM]]].
    repeat split.
    + eapply multi_step. eapply SSLAdd. eapply H. assumption.
    + eapply multi_step. eapply SSLMul. eapply H. assumption.
    + eapply multi_step. eapply SSRAdd. eapply H. assumption.
    + eapply multi_step. eapply SSRMul. eapply H. assumption.
Qed.

Lemma lemma2 :
  forall e e' s s' s'' n,
    (e, s) --> (e', s'')  ->
    lstep (e', s'') (n, s') ->
      lstep (e, s) (n, s').
Proof.
  (* part of the homework *)
Admitted.

Theorem semantic_equivalence :
  forall e s s' n, lstep (e, s) (n, s') <-> (e, s) -->* (EInt n, s').
Proof.
  unfold iff; split.
  - generalize dependent n.
    generalize dependent s'.
    generalize dependent s.
    induction e; intros; inversion H; subst.
    + eapply multi_step. eapply SSVar. eapply multi_refl.
    + eapply multi_refl.
    + specialize (IHe1 s s'0 n0 H2).
      specialize (IHe2 s'0 s' m H6).
      destruct (lemma1 e1 s s'0 n0 IHe1 n0 e2) as [HLA1 ?].
      destruct (lemma1 e2 s'0 s' m IHe2 n0 e2) as [? [? [HRA1 ?]]].
      eapply multi_split. eapply multi_split. eapply HLA1. eapply HRA1.
      eapply multi_step. eapply SSAdd.
      eapply multi_refl.
    + specialize (IHe1 s s'0 n0 H2).
      specialize (IHe2 s'0 s' m H6).
      destruct (lemma1 e1 s s'0 n0 IHe1 n0 e2) as [? HLM1].
      destruct (lemma1 e2 s'0 s' m IHe2 n0 e2) as [? [? [? HRM1]]].
      eapply multi_split. eapply multi_split. eapply HLM1. eapply HRM1.
      eapply multi_step. eapply SSMul.
      eapply multi_refl.
    + specialize (IHe1 s s'0 n0 H2).
      specialize (IHe2 (StoreUpdate s'0 v n0) s' n H7).
      specialize (lemma1Asg e1 s s'0 n0 IHe1 v e2).
      intros L.
      eapply multi_split. eapply L. eapply IHe2.
  - intros. dependent induction H.
    + constructor.
    + destruct y as (e'',s'').
      specialize (IHmulti e'' s'' s' n).
      assert ((e'', s'') ~= (e'', s'')) as T1 by reflexivity.
      assert ((EInt n, s') ~= (EInt n, s')) as T2 by reflexivity.
      specialize (IHmulti T1 T2).
      eapply lemma2; eassumption.
Qed.
