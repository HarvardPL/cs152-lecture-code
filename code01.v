From Coq Require Import ZArith.ZArith.
From Coq Require Import Strings.String.
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
| EMul : Exp -> Exp -> Exp.

Fixpoint eval (exp: Exp) (env: Var -> Int) :=
  match exp with
  | EVar x => env x
  | EInt n => n
  | EAdd e1 e2 => Int_add (eval e1 env) (eval e2 env)
  | EMul e1 e2 => Int_mul (eval e1 env) (eval e2 env)
  end.

Eval compute in eval (EInt 1%Z) (fun x => 0%Z).
Eval compute in eval (EAdd (EInt 2%Z) (EInt 1%Z)) (fun x => 0%Z).

Theorem eadd_commutes: forall env e1 e2,
    eval (EAdd e1 e2) env = eval (EAdd e2 e1) env.
Proof.
  intros.
  simpl. unfold Int_add. rewrite Z.add_comm. reflexivity.
Qed.
