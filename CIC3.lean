/-
We can actually build an expression that the result type of an expression is part of the expression itself. So an ill-typed term cannot even be constructed/type chekced.
-/

inductive Ty where
  | nat
  | bool
deriving Repr, DecidableEq

abbrev Ty.denote : Ty → Type
  | .nat  => Nat
  | .bool => Bool

inductive Expr : Ty → Type where
  | nat  : Nat → Expr .nat
  | bool : Bool → Expr .bool
  | add  : Expr .nat → Expr .nat → Expr .nat
  | le   : Expr .nat → Expr .nat → Expr .bool
  | ite  : Expr .bool → Expr t → Expr t → Expr t
deriving Repr

def eval : Expr t → Ty.denote t
  | .nat n      => n
  | .bool b     => b
  | .add e₁ e₂  => eval e₁ + eval e₂
  | .le e₁ e₂   => decide (eval e₁ <= eval e₂)
  | .ite c e₁ e₂ => if eval c then eval e₁ else eval e₂

def ex : Expr .nat :=
  .ite (.le (.nat 3) (.nat 5))
    (.add (.nat 10) (.nat 20))
    (.nat 0)

#eval eval ex    -- 30

-- def bad : Expr .nat := .add (.bool true) (.nat 3)
-- def bad2 : Expr .nat := .ite (.bool true) (.nat 1) (.bool false)

/-
We can also write transformations that preserve typing by construction.
-/
def constFold : Expr t → Expr t
  | .nat n => .nat n
  | .bool b => .bool b
  | .add e₁ e₂ =>
      let e₁' := constFold e₁
      let e₂' := constFold e₂
      match e₁', e₂' with
      | .nat n₁, .nat n₂ => .nat (n₁ + n₂)
      | _, _ => .add e₁' e₂'
  | .le e₁ e₂ =>
      let e₁' := constFold e₁
      let e₂' := constFold e₂
      match e₁', e₂' with
      | .nat n₁, .nat n₂ => .bool (decide (n₁ <= n₂))
      | _, _ => .le e₁' e₂'
  | .ite c e₁ e₂ =>
      let c' := constFold c
      let e₁' := constFold e₁
      let e₂' := constFold e₂
      match c' with
      | .bool true => e₁'
      | .bool false => e₂'
      | _ => .ite c' e₁' e₂'

def ex2 : Expr .nat :=
  .add (.nat 7)
    (.ite (.le (.nat 2) (.nat 1))
      (.nat 100)
      (.add (.nat 20) (.nat 15)))

#eval ex2
#eval constFold ex2
#eval eval ex2
#eval eval (constFold ex2)

example : constFold ex2 = .nat 42 := rfl
example : eval ex2 = 42 := rfl
