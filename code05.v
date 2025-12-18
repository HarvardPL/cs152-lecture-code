From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Program.Equality.

Definition Var := string.
Definition Var_eq := String.eqb.
Definition Int := Z.
Definition Int_add := Z.add.
Definition Int_mul := Z.mul.

Inductive AExp :=
  | AEVar : Var -> AExp
  | AEInt : Int -> AExp
  | AEAdd : AExp -> AExp -> AExp
  | AEMul : AExp -> AExp -> AExp.

Inductive BExp :=
  | Btrue : BExp
  | Bfalse : BExp
  | BLt : AExp -> AExp -> BExp.

Inductive Com :=
  | CSkip : Com
  | CAsst : Var -> AExp -> Com
  | CSeq : Com -> Com -> Com
  | CITE : BExp -> Com -> Com -> Com
  | CWhile : BExp -> Com -> Com.

Definition Store := Var -> Int.

Definition StoreUpdate (s : Store) (x : Var) (n : Int) : Store :=
  fun (y : Var) => if (Var_eq x y) then n else (s y).

Inductive ASStep : (AExp * Store) -> (AExp * Store) -> Prop :=
  | ASSVar : forall x s,
               ASStep (AEVar x, s) (AEInt (s x), s)
  | ASSAdd : forall n m s,
               ASStep (AEAdd (AEInt n) (AEInt m), s) (AEInt (Int_add n m), s)
  | ASSMul : forall n m s,
               ASStep (AEMul (AEInt n) (AEInt m), s) (AEInt (Int_mul n m), s)
  | AELAdd : forall a1 a1' a2 s,
               ASStep (a1, s) (a1', s) ->
                 ASStep (AEAdd a1 a2, s) (AEAdd a1' a2, s)
  | AELMul : forall a1 a1' a2 s,
               ASStep (a1, s) (a1', s) ->
                 ASStep (AEMul a1 a2, s) (AEMul a1' a2, s)
  | AERAdd : forall n a2 a2' s,
               ASStep (a2, s) (a2', s) ->
                 ASStep (AEAdd (AEInt n) a2, s) (AEAdd (AEInt n) a2', s).

Inductive BSStep : (BExp * Store) -> (BExp * Store) -> Prop :=
  | BSSLt_t : forall n m s,
                (n < m)%Z ->
                  BSStep (BLt (AEInt n) (AEInt m), s) (Btrue, s)
  | BSSLt_f : forall n m s,
                (n >= m)%Z ->
                  BSStep (BLt (AEInt n) (AEInt m), s) (Bfalse, s)
  | BSSLlt  : forall a1 a1' a2 s,
                ASStep (a1, s) (a1', s) ->
                  BSStep (BLt a1 a2, s) (BLt a1' a2, s)
  | BSSRlt  : forall n a2 a2' s,
                ASStep (a2, s) (a2', s) ->
                  BSStep (BLt (AEInt n) a2, s) (BLt (AEInt n) a2', s).

Inductive CSStep : (Com * Store) -> (Com * Store) -> Prop :=
  | CSSSeq   : forall c2 s,
                 CSStep (CSeq (CSkip) c2, s) (c2, s)
  | CSSAsst  : forall n x s,
                 CSStep (CAsst x (AEInt n), s) (CSkip, StoreUpdate s x n)
  | CSSITE_t : forall c1 c2 s,
                 CSStep (CITE Btrue c1 c2, s) (c1, s)
  | CSSITE_f : forall c1 c2 s,
                 CSStep (CITE Bfalse c1 c2, s) (c2, s)
  | CSSSeq1  : forall c1 c1' c2 s s',
                 CSStep (c1, s) (c1', s') ->
                   CSStep (CSeq c1 c2, s) (CSeq c1' c2, s')
  | CSSAsst1 : forall x a a' s,
                 ASStep (a, s) (a', s) ->
                   CSStep (CAsst x a, s) (CAsst x a', s)
  | CSSITE1  : forall b b' c1 c2 s,
                 BSStep (b, s) (b', s) ->
                   CSStep (CITE b c1 c2, s) (CITE b' c1 c2, s)
  | CSSWhile : forall b c s,
                 CSStep (CWhile b c, s) (CITE b (CSeq c (CWhile b c)) CSkip, s).


Inductive ALStep : (AExp * Store) -> Z -> Prop :=
  | ALSInt : forall n s,
               ALStep (AEInt n, s) n
  | ALSVar : forall x s,
               ALStep (AEVar x, s) (s x)
  | ALSAdd : forall n1 n2 a1 a2 s,
               ALStep (a1, s) n1 ->
               ALStep (a2, s) n2 ->
                 ALStep (AEAdd a1 a2, s) (n1+n2)
  | ALSMul : forall n1 n2 a1 a2 s,
               ALStep (a1, s) n1 ->
               ALStep (a2, s) n2 ->
                 ALStep (AEMul a1 a2, s) (n1*n2).

Inductive BLStep : (BExp * Store) -> bool -> Prop :=
  | BLStrue  : forall s,
                 BLStep (Btrue, s) true
  | BLSfalse : forall s,
                 BLStep (Bfalse, s) false
  | BLSlt_t  : forall n m a1 a2 s,
                 ALStep (a1, s) n ->
                 ALStep (a2, s) m ->
                 (n < m)%Z ->
                   BLStep (BLt a1 a2, s) true
  | BLSlt_f  : forall n m a1 a2 s,
                 ALStep (a1, s) n ->
                 ALStep (a2, s) m ->
                 (n >= m)%Z ->
                   BLStep (BLt a1 a2, s) false.

Inductive CLStep : (Com * Store) -> Store -> Prop :=
  | CLSSkip    : forall s,
                   CLStep (CSkip, s) s
  | CLSAsst    : forall n x a s,
                   ALStep (a, s) n ->
                     CLStep (CAsst x a, s) (StoreUpdate s x n)
  | CLSSeq     : forall c1 c2 s s' s'',
                   CLStep (c1, s) s' ->
                   CLStep (c2, s') s'' ->
                     CLStep (CSeq c1 c2, s) s''
  | CLSITE_t   : forall b c1 c2 s s',
                   BLStep (b, s) true ->
                   CLStep (c1, s) s' ->
                     CLStep (CITE b c1 c2, s) s'
  | CLSITE_f   : forall b c1 c2 s s',
                   BLStep (b, s) false ->
                   CLStep (c2, s) s' ->
                     CLStep (CITE b c1 c2, s) s'
  | CLSWhile_f : forall b c s,
                   BLStep (b, s) false ->
                     CLStep (CWhile b c, s) s
  | CLSWhile_t : forall b c s s' s'',
                   BLStep (b, s) true ->
                   CLStep (c, s) s' ->
                   CLStep (CWhile b c, s') s'' ->
                     CLStep (CWhile b c, s) s''.

Definition equiv (c c' : Com) : Prop := forall s s', CLStep (c, s) s' <-> CLStep (c', s) s'.

Theorem While_ITE_equiv_explore :
  forall b c, equiv (CWhile b c) (CITE b (CSeq c (CWhile b c)) CSkip).
Proof.
  unfold equiv. unfold iff. split; intros.
  - inversion H; subst.
    + eapply CLSITE_f. assumption. apply CLSSkip.
    + apply CLSITE_t. assumption. eapply CLSSeq. eassumption. assumption.
  - inversion H; subst; inversion H6; subst.
    + eapply CLSWhile_t. eassumption. eassumption. assumption.
    + apply CLSWhile_f. assumption.
Qed.

Theorem While_ITE_equiv :
  forall b c, equiv (CWhile b c) (CITE b (CSeq c (CWhile b c)) CSkip).
Proof.
  unfold equiv. unfold iff. split; intros.
  - inversion H; subst.
    + apply CLSITE_f; auto. apply CLSSkip.
    + apply CLSITE_t; auto. now apply CLSSeq with (s' := s'0).
  - inversion H; subst.
    + inversion H6; subst. now apply CLSWhile_t with (s' := s'0).
    + inversion H6; subst. now apply CLSWhile_f.
Qed.

(* more automation *)
Theorem While_ITE_equiv2 :
  forall b c, equiv (CWhile b c) (CITE b (CSeq c (CWhile b c)) CSkip).
Proof.
  unfold equiv, iff. split; intros;
  inversion H; try inversion H6; subst; eauto using CLStep.
Qed.

(* reasoning about non-termination,
   assuming non-stuck *)
Theorem infinite_SS: forall s, ~exists s',
  CSStep (CWhile Btrue CSkip, s) (CSkip, s').
  (* For any s, there exists no s', such that
    <While true skip, s> --> <skip, s'> *)
Proof.                           
  intros. unfold "~".
  (* We need to show that
     for any s,
     (there exists s', such that <While true skip, s> --> <skip, s'>)
     implies a contradiction. *)
  intros.
  destruct H as [s' H].
  (* Call H the statement <While true skip, s> --> <skip, s'> .*)
  inversion H.
  (* By inversion, nothing is left. *)
Qed.

Theorem infinite_LS: forall s, ~exists s',
  CLStep (CWhile Btrue CSkip, s) s'.
  (* for any s, <While true skip,s> does not take a large step. *)
Proof.
  intros. unfold "~". intros.
  (* We need to show that
     for any s,
     (While true skip takes a large step)
     implies a contradiction. *)
  destruct H as [s' H].
  dependent induction H.
  - inversion H.
    (* Contradiction: <true,s> does not evaluate to false. *)
  - eapply IHCLStep2. reflexivity.
    (* By the IH for the evaluation of <While true skip,s>. *)
Qed.
